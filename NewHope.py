#
# NewHope key exchange algorithm.
#
# This class implements the standard "ref" version of the New Hope
# algorithm.
#
# @see NewHopeTor




class NewHope:
    # from Params.h


    PARAM_N = 1024
    PARAM_Q = 12289
    POLY_BYTES = 1792
    SEEDBYTES = 32
    RECBYTES = 256

    SENDABYTES = POLY_BYTES + SEEDBYTES

    SENDBBYTES = POLY_BYTES + RECBYTES

    SHAREDBYTES = 32

    qinv = 12287  # -inverse_mod(p, 2 ^ 18)
    rlog = 18


    @staticmethod
    def barrett_reduce(a):
        a &= 0xffff
        u = (a * 5) >> 16
        u *= PARAM_Q
        a -= u
        return a & 0xffff


    @staticmethod
    def montgomery_reduce(a):
        u = (a * NewHope.qinv)
        u &= ((1 << NewHope.rlog) - 1)
        u *= PARAM_Q
        a = a + u
        return a >> 18



    #-------------- error_correction.c --------------

    @staticmethod
    def abs(v):
        mask = v >> 31
        return (v ^ mask) - mask

    @staticmethod
    def f(v0, v0offset, v1, v1offset, x):
        # Next 6 lines compute t = x / PARAM_Q

        b = x * 2730
        t = b >> 25
        b = x - t * 12289
        b = 12288 - b
        b >>= 31
        t -= b

        r = t & 1
        xit = (t >> 1)
        v0[v0offset] = xit + r # v0 = round(x / (2 * PARAM_Q))

        t -= 1
        r = t & 1
        v1[v1offset] = (t >> 1) + r

        return abs(x - ((v0[v0offset]) * 2 * PARAM_Q))

    @staticmethod
    def g(x):

        # Next 6 lines compute t = x / (4 * PARAM_Q)
        b = x * 2730
        t = b >> 27
        b = x - t * 49156
        b = 49155 - b
        b >>= 31
        t -= b

        c = t & 1
        t = (t >> 1) + c # t = round(x / (8 * PARAM_Q))

        t *= 8 * PARAM_Q

        return abs(t - x)

    @staticmethod
    def LDDecode(xi0, xi1, xi2, xi3):

        t = NewHope.g(xi0)
        t += NewHope.g(xi1)
        t += NewHope.g(xi2)
        t += NewHope.g(xi3)

        t -= 8 * PARAM_Q
        t >>= 31
        return t & 1


    @staticmethod
    def crypto_stream_chacha20(c, coffset, clen, n, k):
        blknum = 0
        if clen <= 0:
            return

        while clen >= 64:
            NewHope.crypto_core_chacha20(c, coffset, n, blknum, k)
            blknum+=1
            clen -= 64
            coffset += 64

        if clen != 0:
            block = [None] * 64
            try:
                NewHope.crypto_core_chacha20(block, 0, n, blknum, k)
                i=0
                while i < clen:
                    c[coffset+i] = block[i]
                    i+=1
            finally:
                block = [None] * 64

    # // -------------- crypto_stream_chacha20.c - -------------

    # Based on the public domain implemntation in
    # crypto_stream / chacha20 / e / ref
    # from http: // bench.cr.yp.to / supercop.html byDaniel J.Bernstein

    @staticmethod
    def load_littleendian(x, offset):

        return (x[offset + 0] & 0xff) | (((int)(x[offset + 1] & 0xff)) << 8)\
               | (((int)(x[offset + 2] & 0xff)) << 16) | (((int)(x[offset + 3] & 0xff)) << 24)


    @staticmethod
    def store_littleendian(x,offset, u):
        x[offset + 0] = u
        u >>= 8
        x[offset + 1] = u
        u >>= 8
        x[offset + 2] = u
        u >>= 8
        x[offset + 3] = u


    @staticmethod
    def crypto_core_chacha20(out, outOffset, nonce, blknum, k):


        j0 = x0 = 0x61707865 # "expa"
        j1 = x1 = 0x3320646e # "nd 3"
        j2 = x2 = 0x79622d32 # "2-by"
        j3 = x3 = 0x6b206574 # "te k"
        j4 = x4 = NewHope.load_littleendian(k, 0)
        j5 = x5 = NewHope.load_littleendian(k, 4)
        j6 = x6 = NewHope.load_littleendian(k, 8)
        j7 = x7 = NewHope.load_littleendian(k, 12)
        j8 = x8 = NewHope.load_littleendian(k, 16)
        j9 = x9 = NewHope.load_littleendian(k, 20)
        j10 = x10 = NewHope.load_littleendian(k, 24)
        j11 = x11 = NewHope.load_littleendian(k, 28)
        j12 = x12 = blknum
        j13 = x13 = 0
        j14 = x14 = nonce
        j15 = x15 = (nonce >> 32)

        i=20
        while(i>0):
            x0 += x4
            x12 ^= x0
            x12 = (x12 << 16) | (x12 >> 16)
            x8 += x12
            x4 ^= x8
            x4 = (x4 << 12) | (x4 >> 20)
            x0 += x4
            x12 ^= x0
            x12 = (x12 << 8) | (x12 >> 24)
            x8 += x12
            x4 ^= x8
            x4 = (x4 << 7) | (x4 >> 25)
            x1 += x5
            x13 ^= x1
            x13 = (x13 << 16) | (x13 >> 16)
            x9 += x13
            x5 ^= x9
            x5 = (x5 << 12) | (x5 >> 20)
            x1 += x5
            x13 ^= x1
            x13 = (x13 << 8) | (x13 >> 24)
            x9 += x13
            x5 ^= x9
            x5 = (x5 << 7) | (x5 >> 25)
            x2 += x6
            x14 ^= x2
            x14 = (x14 << 16) | (x14 >>16)
            x10 += x14
            x6 ^= x10
            x6 = (x6 << 12) | (x6 >> 20)
            x2 += x6
            x14 ^= x2
            x14 = (x14 << 8) | (x14 >> 24)
            x10 += x14
            x6 ^= x10
            x6 = (x6 << 7) | (x6 >> 25)
            x3 += x7
            x15 ^= x3
            x15 = (x15 << 16) | (x15 >> 16)
            x11 += x15
            x7 ^= x11
            x7 = (x7 << 12) | (x7 >> 20)
            x3 += x7
            x15 ^= x3
            x15 = (x15 << 8) | (x15 >> 24)
            x11 += x15
            x7 ^= x11
            x7 = (x7 << 7) | (x7 >> 25)
            x0 += x5
            x15 ^= x0
            x15 = (x15 << 16) | (x15 >> 16)
            x10 += x15
            x5 ^= x10
            x5 = (x5 << 12) | (x5 >> 20)
            x0 += x5
            x15 ^= x0
            x15 = (x15 << 8) | (x15 >> 24)
            x10 += x15
            x5 ^= x10
            x5 = (x5 << 7) | (x5 >> 25)
            x1 += x6
            x12 ^= x1
            x12 = (x12 << 16) | (x12 >> 16)
            x11 += x12
            x6 ^= x11
            x6 = (x6 << 12) | (x6 >> 20)
            x1 += x6
            x12 ^= x1
            x12 = (x12 << 8) | (x12 >> 24)
            x11 += x12
            x6 ^= x11
            x6 = (x6 << 7) | (x6 >> 25)
            x2 += x7
            x13 ^= x2
            x13 = (x13 << 16) | (x13 >> 16)
            x8 += x13
            x7 ^= x8
            x7 = (x7 << 12) | (x7 >> 20)
            x2 += x7
            x13 ^= x2
            x13 = (x13 << 8) | (x13 >> 24)
            x8 += x13
            x7 ^= x8
            x7 = (x7 << 7) | (x7 >> 25)
            x3 += x4
            x14 ^= x3
            x14 = (x14 << 16) | (x14 >> 16)
            x9 += x14
            x4 ^= x9
            x4 = (x4 << 12) | (x4 >> 20)
            x3 += x4
            x14 ^= x3
            x14 = (x14 << 8) | (x14 >> 24)
            x9 += x14
            x4 ^= x9
            x4 = (x4 << 7) | (x4 >> 25)
            i -= 2


        x0 += j0
        x1 += j1
        x2 += j2
        x3 += j3
        x4 += j4
        x5 += j5
        x6 += j6
        x7 += j7
        x8 += j8
        x9 += j9
        x10 += j10
        x11 += j11
        x12 += j12
        x13 += j13
        x14 += j14
        x15 += j15

        NewHope.store_littleendian(out, outOffset + 0, x0)
        NewHope.store_littleendian(out, outOffset + 4, x1)
        NewHope.store_littleendian(out, outOffset + 8, x2)
        NewHope.store_littleendian(out, outOffset + 12, x3)
        NewHope.store_littleendian(out, outOffset + 16, x4)
        NewHope.store_littleendian(out, outOffset + 20, x5)
        NewHope.store_littleendian(out, outOffset + 24, x6)
        NewHope.store_littleendian(out, outOffset + 28, x7)
        NewHope.store_littleendian(out, outOffset + 32, x8)
        NewHope.store_littleendian(out, outOffset + 36, x9)
        NewHope.store_littleendian(out, outOffset + 40, x10)
        NewHope.store_littleendian(out, outOffset + 44, x11)
        NewHope.store_littleendian(out, outOffset + 48, x12)
        NewHope.store_littleendian(out, outOffset + 52, x13)
        NewHope.store_littleendian(out, outOffset + 56, x14)
        NewHope.store_littleendian(out, outOffset + 60, x15)



    @staticmethod
    def helprec(c, v, seed, nonce):

        v0 = [0] * 8
        rand = [0] * 32


        try:
            NewHope.crypto_stream_chacha20(rand, 0, 32, (nonce << 56), seed)
            i=0
            while i < 256:
                rbit = (rand[i >> 3] >> (i & 7)) & 1

                k  = NewHope.f(v0, 0, v0, 4, 8 * v.coeffs[0+i] + 4 * rbit)
                k += NewHope.f(v0, 1, v0, 5, 8 * v.coeffs[256+i] + 4 * rbit)
                k += NewHope.f(v0, 2, v0, 6, 8 * v.coeffs[512+i] + 4 * rbit)
                k += NewHope.f(v0, 3, v0, 7, 8 * v.coeffs[768+i] + 4 * rbit)

                k = (2 * PARAM_Q-1-k) >> 31

                v_tmp0 = ((~k) & v0[0]) ^ (k & v0[4])
                v_tmp1 = ((~k) & v0[1]) ^ (k & v0[5])
                v_tmp2 = ((~k) & v0[2]) ^ (k & v0[6])
                v_tmp3 = ((~k) & v0[3]) ^ (k & v0[7])

                c.coeffs[0+i] = ((v_tmp0 -   v_tmp3) & 3)
                c.coeffs[256+i] = ((v_tmp1 -   v_tmp3) & 3)
                c.coeffs[512+i] = ((v_tmp2 -   v_tmp3) & 3)
                c.coeffs[768+i] = ((   -k  + 2 * v_tmp3) & 3)

                i+=1
        finally:
                v0 = [0] * 8
                rand = [0] * 32

    # // -------------- poly.c - -------------


class _Poly:
    def __init__(self):
        self.coeffs = [0] * NewHope.PARAM_N

    def frombytes(self, a, offset):

        i = 0
        while i < (NewHope.PARAM_N / 4):
            self.coeffs[4 * i + 0] = ((a[offset + 7 * i + 0] & 0xff) | ((a[offset + 7 * i + 1] & 0x3f) << 8))
            self.coeffs[4 * i + 1] = (((a[offset + 7 * i + 1] & 0xc0) >> 6) | ((a[offset + 7 * i + 2] & 0xff) << 2) | (
            (a[offset + 7 * i + 3] & 0x0f) << 10))
            self.coeffs[4 * i + 2] = (((a[offset + 7 * i + 3] & 0xf0) >> 4) | ((a[offset + 7 * i + 4] & 0xff) << 4) | (
            (a[offset + 7 * i + 5] & 0x03) << 12))
            self.coeffs[4 * i + 3] = (((a[offset + 7 * i + 5] & 0xfc) >> 2) | ((a[offset + 7 * i + 6] & 0xff) << 6))
            i += 1

    def tobytes(self, r, offset):

        i = 0
        while i < (NewHope.PARAM_N / 4):
            t0 = NewHope.barrett_reduce(self.coeffs[4 * i + 0])  # // Make sure that coefficients have only 14 bits
            t1 = NewHope.barrett_reduce(self.coeffs[4 * i + 1])
            t2 = NewHope.barrett_reduce(self.coeffs[4 * i + 2])
            t3 = NewHope.barrett_reduce(self.coeffs[4 * i + 3])

            m = t0 - PARAM_Q
            c = m
            c >>= 15
            t0 = m ^ ((t0 ^ m) & c)  # Make sure that coefficients are in[0, q]

            m = t1 - NewHope.PARAM_Q
            c = m
            c >>= 15
            t1 = m ^ ((t1 ^ m) & c)  # Make sure that coefficients are in[0, q]

            m = t2 - PARAM_Q
            c = m
            c >>= 15
            t2 = m ^ ((t2 ^ m) & c)  # Make sure that coefficients are in[0, q]

            m = t3 - PARAM_Q
            c = m
            c >>= 15
            t3 = m ^ ((t3 ^ m) & c)  # Make sure that coefficients are in[0, q]

            r[offset + 7 * i + 0] = (t0 & 0xff)
            r[offset + 7 * i + 1] = ((t0 >> 8) | (t1 << 6))
            r[offset + 7 * i + 2] = (t1 >> 2)
            r[offset + 7 * i + 3] = ((t1 >> 10) | (t2 << 4))
            r[offset + 7 * i + 4] = (t2 >> 4)
            r[offset + 7 * i + 5] = ((t2 >> 12) | (t3 << 2))
            r[offset + 7 * i + 6] = (t3 >> 6)
