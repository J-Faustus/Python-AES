"""Handle everything related to AES-128, -192, or -256"""

#https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf

modes=['ECB', 'CBC', 'CFB', 'OFB', 'CTR']

def rotate(value:int, places:int, nbits:int):
    '''rotate right by places bits'''
    if places==0:return value
    if value.bit_length()>nbits:raise ValueError("Value given could not be fit in the given number of bits")
    # value=bin(value).removeprefix('0b').zfill(nbits)
    # if len(value)>nbits:raise ValueError("A value too large for the number of bits was given")

    # if places>0:#right rotate
    #     value=value[len(value)-places:]+value[:len(value)-places]
    # else:#left rotate
    #     places*=-1
    #     value=value[places:]+value[:places]
    # return int(value, 2)
    if places>=0:
        value, remainder=divmod(value, 2**places)#value is the first set of bits, remainder is the second. Place remainder before value
        return (remainder<<(nbits-places))+value#bitshift remainder by enough to place it at the beginning of the number
    else:
        value, remainder=divmod(value, 2**(nbits-abs(places)))#value becomes the first places bits. Remainder is nbits-places bits.
        return (remainder<<abs(places))+value

#Rijndael modulo function
def RijndaelModulo(a:int):
    '''Reduce a number within the Rijndael field'''
    #find the highest order bit in a and xor with the Rijndael field polynomial
    while a.bit_length()>8:
        a^=0x11b*pow(2,a.bit_length()-9)
    return a

#multiply in the Rijndael field GF(2^8)/(x^8+x^4+x^3+x+1)
def RijndaelMultiply(a:int, b:int):
    '''multiply two numbers within the Rijndael field'''
    # a=bin(a).removeprefix('0b').zfill(8)
    # b=bin(b).removeprefix('0b').zfill(8)
    # product=[]
    # for i,bit in enumerate(a):
    #     if bit=='0':continue
    #     product.append(int(b+'0'*(7-i),2))#shift b as necessary
    # temp=0
    # for i in product:
    #     temp^=i
    # return RijndaelModulo(temp)

    temp=0
    for i in range(b.bit_length()):
        if b&(2**i):temp^=(a<<i)
    return RijndaelModulo(temp)

#generate the multiplication table for GF(2^8)/(x^8+x^4+x^3+x+1)
_GFmultiplicationtable=[[RijndaelMultiply(i,j) for i in range(256)] for j in range(256)]

#multiplicative inverses in GF(2^8)/(x^8+x^4+x^3+x+1)
_GFmultiplicativeinverses=[0]+[_GFmultiplicationtable[i].index(1) for i in range(1,256)]

def Rijndaelmultiply(a,b):#don't calculate anymore. all values are precomputed
    '''multiply two numbers in the Rijndael field'''
    return _GFmultiplicationtable[a][b]

def Rijndaeladd(a,b):
    '''Rijndael field addition and subtraction operation'''
    if b!=RijndaelModulo(b) or a !=RijndaelModulo(a):raise ValueError("Not a number in Rijndael's field")
    return a^b

#generate the s-box
sbox=[]
for i in range(256):
    i=_GFmultiplicativeinverses[i]
    sbox.append(i^rotate(i,-1,8)^rotate(i,-2,8)^rotate(i,-3,8)^rotate(i,-4,8)^99)

#generate the inverse s-box
isbox=[]
for i in range(256):
    isbox.append(_GFmultiplicativeinverses[rotate(i,-1,8)^rotate(i,-3,8)^rotate(i,-6,8)^5])

#ensure the sbox and invsbox actually work
for i in range(256):assert i==isbox[sbox[i]], "The substitution boxes failed"

class AESblock:
    """handle one block of an AES encryption"""
    def __init__(self):
        #data is stored as a 2d list of rows of bytes
        self._datamatrix=[[0]*4 for i in range(4)]

    def sequence(self):
        '''return a generator for the bytes of the datamatrix in column-major order'''
        for c in range(4):
            for r in range(4):
                yield int.to_bytes(self._datamatrix[r][c])

    @property
    def data(self):#data is inputted and outputted as bytes, but internally stored as integers
        '''Data stored in the block'''
        # d=b''
        # for column in range(4):
        #     for row in range(4):
        #         d+=int.to_bytes(self._datamatrix[row][column])
        # return d
        return b''.join(self.sequence())
    
    @data.setter
    def data(self, value):
        if not isinstance(value, bytes):raise ValueError("AES Block cannot have non-bytes value")
        #value will be right-padded with zero until 16 bytes
        if len(value)>16:raise ValueError("AES Block cannot have more than 16 bytes")
        # value=list(value)
        # while len(value)<16:
        #     value.append(0)
        value=value.ljust(16, b'\x00')
        for column in range(4):
            for row in range(4):
                self._datamatrix[row][column]=value[row+4*column]
    
    @data.deleter
    def data(self):
        del self._datamatrix
    
    def subbytes(self):
        '''perform the substitution step'''
        for r,i in enumerate(self._datamatrix):
            for c,b in enumerate(i):
                self._datamatrix[r][c]=sbox[b]

    def shiftrows(self):
        '''perform the shiftrows step'''
        for r,i in enumerate(self._datamatrix):
            for j in range(r):
                i.append(i.pop(0))

    def addroundkey(self, roundkey):
        '''add the round key as a matrix of values'''
        for r,i in enumerate(self._datamatrix):
            for c,b in enumerate(i):
                self._datamatrix[r][c]=Rijndaeladd(b,roundkey[r+4*c])

    def mixcolumns(self):#TODO: fix the slowness of this step (done?)
        '''perform the mixcolumns step'''
        for c in range(4):
            column=[self._datamatrix[i][c] for i in range(3, -1, -1)]#the highest order coefficient is at the bottom of the matrix, but the first in the list, so reverse
            #the column contains the coefficients of a polynomial over GF(2^8)
            #multiply by fixed polynomial 3x^3+x^2+x+2 modulo x^4+1
            if False:#this is the more readable version, but it's slower since it explicitly performs a polynomial product
                product=[0]*7#coefficients of the product polynomial
                for i,a in enumerate([3,1,1,2]):
                    for j,b in enumerate(column):
                        product[i+j]=Rijndaeladd(product[i+j],RijndaelMultiply(a,b))
                #reduce the polynomial modulo x^4+1
                column=[product[3]]+[Rijndaeladd(product[i],product[i+4]) for i in range(3)]
                column.reverse()#the highest order coefficient is at the bottom of the matrix, so we reverse again
                for i in range(4):self._datamatrix[i][c]=column[i]
            else:
                #directly compute the matrix entries
                self._datamatrix[3][c]=RijndaelModulo((column[3]<<1)^(column[3])^(column[2])^(column[1])^(column[0]<<1))
                self._datamatrix[2][c]=RijndaelModulo((column[0]<<1)^(column[0])^(column[3])^(column[2])^(column[1]<<1))
                self._datamatrix[1][c]=RijndaelModulo((column[1]<<1)^(column[1])^(column[0])^(column[3])^(column[2]<<1))
                self._datamatrix[0][c]=RijndaelModulo((column[2]<<1)^(column[2])^(column[1])^(column[0])^(column[3]<<1))
            

    def invsubbytes(self):
        '''perform the inverse substitution step'''
        for r,i in enumerate(self._datamatrix):
            for c,b in enumerate(i):
                self._datamatrix[r][c]=isbox[b]

    def invshiftrows(self):
        '''perform the inverseshiftrows step'''
        for r,i in enumerate(self._datamatrix):
            if r==0:continue
            for j in range(4-r):
                i.append(i.pop(0))

    def invaddroundkey(self, roundkey):
        '''reverse the addroundkey step'''
        for r,i in enumerate(self._datamatrix):
            for c,b in enumerate(i):
                self._datamatrix[r][c]=Rijndaeladd(b,roundkey[r+4*c])

    def invmixcolumns(self):#TODO: fix this step's slowness (done?)
        '''perform the invmixcolumns step'''
        for c in range(4):
            column=[self._datamatrix[i][c] for i in range(3, -1, -1)]#the highest order coefficient is at the bottom of the matrix, but the first in the list, so reverse
            if False:#this is the more readable version, but it's slower since it explicitly performs a polynomial product
                #the column contains the coefficients of a polynomial over GF(2^8)
                #multiply by fixed polynomial 11x^3+13x^2+9x+14 modulo x^4+1
                product=[0]*7#coefficients of the product polynomial
                for i,a in enumerate((11,13,9,14)):
                    for j,b in enumerate(column):
                        product[i+j]=Rijndaeladd(product[i+j],RijndaelMultiply(a,b))
                #reduce the polynomial modulo x^4+1
                column=[product[3]]+[Rijndaeladd(product[i],product[i+4]) for i in range(3)]
                column.reverse()#the highest order coefficient is at the bottom of the matrix, so we reverse again
                for i in range(4):self._datamatrix[i][c]=column[i]
            else:
                #directly compute the matrix entries
                self._datamatrix[3][c]=RijndaelModulo((column[3]<<3)^(column[3]<<1)^(column[3])^(column[2]<<3)^(column[2]<<2)^(column[2])^(column[1]<<3)^(column[1])^(column[0]<<3)^(column[0]<<2)^(column[0]<<1))
                self._datamatrix[2][c]=RijndaelModulo((column[0]<<3)^(column[0]<<1)^(column[0])^(column[3]<<3)^(column[3]<<2)^(column[3])^(column[2]<<3)^(column[2])^(column[1]<<3)^(column[1]<<2)^(column[1]<<1))
                self._datamatrix[1][c]=RijndaelModulo((column[1]<<3)^(column[1]<<1)^(column[1])^(column[0]<<3)^(column[0]<<2)^(column[0])^(column[3]<<3)^(column[3])^(column[2]<<3)^(column[2]<<2)^(column[2]<<1))
                self._datamatrix[0][c]=RijndaelModulo((column[2]<<3)^(column[2]<<1)^(column[2])^(column[1]<<3)^(column[1]<<2)^(column[1])^(column[0]<<3)^(column[0])^(column[3]<<3)^(column[3]<<2)^(column[3]<<1))
    
    def encrypt(self,key,size):
        '''fully encrypt the block using the provided key'''
        schedule=genkeyschedule(key,size)
        self.encryptwithschedule(schedule, size)
    
    def encryptwithschedule(self, schedule, size):
        '''fully encrypt using the provided schedule and size'''
        numrounds={128:9,192:11,256:13}[size]
        self.addroundkey(schedule[0])
        for i in range(numrounds):
            self.subbytes()
            self.shiftrows()
            self.mixcolumns()
            self.addroundkey(schedule[i+1])
        self.subbytes()
        self.shiftrows()
        self.addroundkey(schedule[-1])

    def decrypt(self,key,size):
        '''fully decrypt the block using the provided key'''
        schedule=geninvkeyschedule(key,size)
        self.decryptwithschedule(schedule, size)
    
    def decryptwithschedule(self, schedule, size):
        '''fully decrypt with the provided schedule and size'''
        numrounds={128:9,192:11,256:13}[size]
        self.invaddroundkey(schedule[0])
        for i in range(numrounds):
            self.invshiftrows()
            self.invsubbytes()
            self.invaddroundkey(schedule[i+1])
            self.invmixcolumns()
        self.invshiftrows()
        self.invsubbytes()
        self.invaddroundkey(schedule[-1])

    def xor(self, block):
        '''xor current value with the given block'''
        assert isinstance(block, AESblock), "Cannot xor with a non-block object"
        for r, row in enumerate(self._datamatrix):
            for c, v in enumerate(row):
                self._datamatrix[r][c]=v^block._datamatrix[r][c]

#generate the round constants
#TODO this is broken at values i>10, and it would be nice for it to not be broken, but I don't think it really matters all that much
def rcon(i):
    '''generate the round constant for the ith round'''
    r=1
    for i in range(i-1):
        r=r*2
        if r>128:r^=int('11b',16)
    return r

def SubWord(word):
    '''substitute words for the AES key schedule'''
    bytelist=[0,0,0,0]
    for i in range(4):
        word,bytelist[i]=divmod(word, 256)
    for i,v in enumerate(bytelist):bytelist[i]=sbox[v]
    return sum(bytelist[i]<<(8*(i)) for i in range(4))

def RotWord(word):
    '''rotate words for the AES key schedule'''
    #one-byte left circular shift
    word=int.to_bytes(word, 4)
    assert isinstance(word, bytes)
    word=int.from_bytes(word[1:]+word[0:1])
    return word

#generate the key schedule from a key
def genkeyschedule(key, size):
    '''generate the key schedule from the key'''
    if not isinstance(key, bytes):raise ValueError("Key must be a bytes object")
    if size not in [128, 192, 256]:raise ValueError("Unsupported size")
    size//=8
    if len(key)>size:raise ValueError("Key is too large")
    while len(key)<size:#right pad the key
        key+=b'\x00'
    N=size//4
    key=[int.from_bytes(key[i:i+4]) for i in range(0, 16, 4)]
    #number of round keys needed
    R=N+7
    #initialize the key schedule
    W=[0]*(4*R)
    for word in range(4*R):
        if word<N:
            W[word]=key[word]
        elif word%N==0:
            W[word]=W[word-N]^SubWord(RotWord(W[word-1]))^(rcon(word//N)<<24)
        elif N==8 and word%N==4:
            W[word]=W[word-N]^SubWord(W[word-1])
        else:
            W[word]=W[word-N]^W[word-1]
    keys=[b''.join([int.to_bytes(W[i],4) for i in range(4*round, 4*round+4)]) for round in range(R)]
    #separate into a key schedule and return
    return [list(key) for key in keys]

#generate the key schedule in reverse from a key
def geninvkeyschedule(key,size):
    '''generate the inverse key schedule'''
    k=genkeyschedule(key, size)
    k.reverse()
    return k

def AESencrypt(value, key, size, mode='CBC', IV=b'\x00'*16):
    '''Encrypt a given message using the key padded to the size using the mode'''
    assert isinstance(value, bytes), "Cannot encrypt a non-bytes object"
    assert isinstance(IV, bytes), 'Cannot use a non-bytes object as an initialization vector'
    while len(IV)<16:IV=b'\x00'+IV#TODO: why is this left-padded?
    #set the initialization vector
    vector=AESblock()
    vector.data=IV
    #pad the value to a multiple of 128 bits
    while len(value)%16!=0:value+=b'\x00'
    #make a list of blocks and set their data to the blocks of the message
    blocklist=[AESblock() for i in range(len(value)//16)]
    for i, block in enumerate(blocklist):
        block.data=value[16*i:16*(i+1)]
    if mode=='ECB':#each block is encrypted individually using the same key. Electronic Codebook
        for block in blocklist:
            block.encrypt(key, size)
    elif mode=='CBC':#Cipher Block Chaining. Each block is bitwise xored with the ciphertext of the previous before being encrypted, but the first is xored with an initialization vector
        for i, block in enumerate(blocklist):
            if i==0:block.xor(vector)
            else:block.xor(blocklist[i-1])
            block.encrypt(key, size)
    elif mode=='CFB':#Cipher Feedback Mode. 
        #I don't even know what the pdf at the start of this program is saying for how this mode works, so I give up.
        return NotImplemented
    elif mode=='OFB':#Output feedback mode. The IV is encrypted and used both to xor the plaintext block and as the IV for the next block. This is symmetric (encryption=decryption)
        for block in blocklist:
            vector.encrypt(key, size)
            block.xor(vector)
    elif mode=='CTR':#Counter Mode. Each block is bitwise xored with an encrypted counter. Each block has a unique counter block
        #This will never be implemented because it sucks
        return NotImplemented
    output=b''
    for block in blocklist:
        output+=block.data
    return output

def AESdecrypt(value, key, size, mode='CBC', IV=b'\x00'*16):
    '''Decrypt a given message using the key padded to the size using the mode'''
    assert isinstance(value, bytes), 'Cannot decrypt a non-bytes object'
    assert isinstance(IV, bytes), 'Cannot use a non-bytes object as an initialization vector'
    while len(IV)<16:IV=b'\x00'+IV#TODO: why left padded?
    #set the initialization vector
    vector=AESblock()
    vector.data=IV
    #pad the value to a multiple of 128 bits
    while len(value)%16!=0:value+=b'\x00'
    #make a list of blocks and set their data to the blocks of the message
    blocklist=[AESblock() for i in range(len(value)//16)]
    for i, block in enumerate(blocklist):
        block.data=value[16*i:16*(i+1)]
    if mode=='ECB':#each block is encrypted individually using the same key. Electronic Codebook
        for block in blocklist:
            block.decrypt(key, size)
    elif mode=='CBC':#Cipher Block Chaining. Each block is bitwise xored with the ciphertext of the previous after being decrypted, but the first is xored with an initialization vector
        #decrypt back to front so the xor works (we need to xor with the ciphertext of the previous block, not the plaintext, so we need to xor each block before decrypting the one before it)
        for i, block in reversed(list(enumerate(blocklist))):
            block.decrypt(key, size)
            if i==0:block.xor(vector)
            else:block.xor(blocklist[i-1])
    elif mode=='CFB':#Cipher Feedback Mode. 
        #I don't even know what the pdf at the start of this program is saying for how this mode works, so I give up.
        return NotImplemented
    elif mode=='OFB':#Output feedback mode. The IV is encrypted and used both to xor the plaintext block and as the IV for the next block. This is symmetric (encryption=decryption)
        for block in blocklist:
            vector.encrypt(key, size)
            block.xor(vector)
    elif mode=='CTR':#Counter Mode. Each block is bitwise xored with an encrypted counter. Each block has a unique counter block
        #This will never be implemented because it sucks
        return NotImplemented
    return b''.join(block.data for block in blocklist)

def ECBencryptiongenerator(key, size):
    '''make a generator for encrypting blocks in ECB mode'''
    block=AESblock()
    schedule=genkeyschedule(key, size)
    try:
        while True:
            try:
                block.data=yield block.data
                block.encryptwithschedule(schedule, size)
            except Exception as e:
                yield e
    finally:
        del block, schedule

def ECBdecryptiongenerator(key, size):
    '''make a generator for decrypting blocks in ECB mode'''
    block=AESblock()
    schedule=geninvkeyschedule(key, size)
    try:
        while True:
            try:
                block.data=yield block.data
                block.decryptwithschedule(schedule, size)
            except Exception as e:
                yield e
    finally:
        del block, schedule

def CBCencryptiongenerator(IV, key, size):
    '''make a generator for encrypting blocks in CBC mode'''
    vector=AESblock()
    vector.data=IV
    block=AESblock()
    schedule=genkeyschedule(key, size)
    try:
        while True:
            try:
                block.data=yield block.data
                block.xor(vector)
                block.encryptwithschedule(schedule, size)
                vector.data=block.data
            except Exception as e:
                yield e
    finally:
        del vector, block, schedule

def CBCdecryptiongenerator(IV, key, size):
    '''make a generator for decrypting blocks in CBC mode'''
    vector=AESblock()
    vector.data=IV
    vector2=AESblock()
    block=AESblock()
    schedule=geninvkeyschedule(key, size)
    try:
        while True:
            try:
                block.data=yield block.data
                vector2.data=block.data
                block.decryptwithschedule(schedule, size)
                block.xor(vector)
                vector.data=vector2.data
            except Exception as e:
                yield e
    finally:
        del vector, vector2, block, schedule


if __name__=='__main__':
    #1.1485117971897126e-05 seconds per byte after optimizing encryption and decryption 89.39% faster (3.244603304564953e-05 seconds per byte encrypting and decrypting after optimizing encryption, approximately (0.00010825489584931347 seconds before optimization, now 70% off))
    test=8
    if test==1:#a collection of random tests
        block=AESblock()
        block.data=b'test'
        block.encrypt(b'a', 128)
        block.decrypt(b'a', 128)
        print(block.data)
        print(AESdecrypt(AESencrypt(b'testing testing testing testing testing testing testing ooooooooooooo testing'*256, b'1', 128, mode='ECB'), b'1', 128, mode='ECB'))
        block.data=int.to_bytes(7)
        block2=AESblock()
        block2.data=int.to_bytes(200)
        block.xor(block2)
        print(block.data)
        import time
        k=b'aghuefrio'
        order=2**20
        v=b'\x00'*order
        t=time.time()
        AESdecrypt(AESencrypt(v, k, 128), k, 128)
        print((time.time()-t)/order)
    elif test==2:#16MB timing test
        encrypter=CBCencryptiongenerator(b'test', b'test', 128)
        decrypter=CBCdecryptiongenerator(b'test', b'test', 128)
        encrypter.__next__()
        decrypter.__next__()
        import time
        t=time.time()
        for i in range(1000000):
            decrypter.send(encrypter.send(b'hello'))
        print(time.time()-t)
        #519.1365287303925
        #183.761887550354 after optimizing inverse mix columns
    elif test==3:#key schedule testing
        k=13*b'\x00'+b'boh'
        print(genkeyschedule(k, 128))
    elif test==4:#testing against known test vectors
        #calculators for AES test vectors
        #https://testprotect.com/appendix/AEScalc
        #https://www.ieasynote.com/tools/aes
        a=genkeyschedule(b'\x00', 128)
        schedule=[0]*11
        for c,i in enumerate(a):
            print((k:=''.join(hex(j)[2:].zfill(2) for j in i)))
            schedule[c]=k
        trueschedule=[0x00000000000000000000000000000000,
        0x62636363626363636263636362636363,
        0x9b9898c9f9fbfbaa9b9898c9f9fbfbaa,
        0x90973450696ccffaf2f457330b0fac99,
        0xee06da7b876a1581759e42b27e91ee2b,
        0x7f2e2b88f8443e098dda7cbbf34b9290,
        0xec614b851425758c99ff09376ab49ba7,
        0x217517873550620bacaf6b3cc61bf09b,
        0x0ef903333ba9613897060a04511dfa9f,
        0xb1d4d8e28a7db9da1d7bb3de4c664941,
        0xb4ef5bcb3e92e21123e951cf6f8f188e]
        for i in range(len(schedule)):
            if trueschedule[i]!=int(schedule[i],16):print(i)
        block=AESblock()
        #block data is default nothing
        #default key is nothing
        block.encrypt(b'', 128)
        assert block.data.hex()=='66e94bd4ef8a2c3b884cfa59ca342b2e', "The ciphertext of a single block of nothing using the 128-bit key of nothing is incorrect. Check your programming."
    elif test==5:#timing test for the encryption steps
        block=AESblock()
        import time
        t=time.time()
        for i in range(10000):block.mixcolumns()
        print(f'{time.time()-t:.6f}')
        #in decreasing order of time consumption
        #mixcolumns - .021185
        #addroundkey - .007
        #subbytes - .006
        #shiftrows - .002
    elif test==6:#test vector
        block=AESblock()
        block.data=b'\x84\xc4\xd2f\xb6\xe4\x1f\xc8\x93\xfd\x86.\x08\xcfs\x1d'
        block.decrypt(b'', 128)
        print(block.data)
    elif test==7:#pure encryption test
        block=AESblock()
        import time
        schedule=genkeyschedule(b'00', 128)
        t=time.time()
        for i in range(2**13):
            block.encryptwithschedule(schedule, 128)
        print(time.time()-t)
    elif test==8:#block data setting timing test
        block=AESblock()
        import time
        t=time.time()
        for i in range(10000):
            block.data=b''
        print(time.time()-t)
