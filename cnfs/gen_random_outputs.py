import random
import math

random.seed(0)

BITS_NUM = 512

with open('outputs_' + str(BITS_NUM) + 'bit.txt', 'w') as ofile:
    ofile.write(('0'*BITS_NUM) + '\n')
    ofile.write(('1'*BITS_NUM) + '\n')
    for i in range(1, int(math.log2(BITS_NUM))):
        #print(str(bit_seq_len))
        bit_seq_len = int(math.pow(2, i))
        s = ''
        while len(s) < BITS_NUM:
            s += '1'* bit_seq_len
            s += '0'* bit_seq_len
        assert(len(s) >= BITS_NUM)
        s = s[:BITS_NUM]
        assert(len(s) == BITS_NUM)
        ofile.write(s + '\n')
    for i in range(10):
        s = ''
        for j in range(BITS_NUM):
            s += str(random.randint(0, 1))
        ofile.write(s + '\n')
