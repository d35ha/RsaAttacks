import os, re, random, itertools, multiprocessing, subprocess
try:
    from Crypto.PublicKey import RSA
except:
    print("[-] Cannot import Crypto library")
    print("[-] Use this command in sage shell --> pip install pycryptodome")
    exit()
try:
    from Crypto.PublicKey import _slowmath
except:
    print("[-] Cannot import _slowmath module")
    print("[-] Use this command in sage shell --> cd /opt/sagemath-8.4/local/lib/python2.7/site-packages/Crypto ; wget https://raw.githubusercontent.com/dlitz/pycrypto/master/lib/Crypto/PublicKey/_slowmath.py")
    exit()
try:
    import requests
except:
    print("[-] Cannot import requests library")
    print("[-] Use this command in sage shell --> pip install requests")
    exit()
try:
    from primefac import primefac, pollardRho_brent, pollard_pm1, williams_pp1
except:
    print("[-] Cannot import primefac library")
    print("[-] Use this command in sage shell --> pip install primefac")
    exit()

all_primes = primes
known_primes = [] 

def write_pub_pem(file,n,e,d=0):
    try: 
        if d==0: open(file,'wb').write(RSA.construct((long(n), long(e))).publickey().exportKey())
        else: open(file,'wb').write(RSA.construct((long(n), long(e), long(d))).exportKey(format='PEM'))
    except Exception as err: print("[-] " + str(err))

def read_pub_pem(file):
    n,e,d,p,q,u = 0,0,0,0,0,0
    try: 
        key = RSA.importKey(open(file, 'rb').read())
        try: n = key.n
        except: pass
        try: e = key.e
        except: pass
        try: d = key.d
        except: pass
        try: p = key.p
        except: pass
        try: q = key.q
        except: pass
        try: u = key.u
        except: pass
    except Exception as err: print("[-] " + str(err))
    return n,e,d,p,q,u

def clc_n_phi(primes):
    n, phi = 1, 1
    for prime in primes: n *= prime; phi *= prime - 1
    if len(primes) == 1 : phi *= prime - 1
    return n,phi

def two_lists_permutations(list1,list2):
    if len(list1) != len(list2): return []
    used_indeces = []
    perm_list_1 = []
    perm_list_2 = []
    for i1, i2 in itertools.permutations(range(len(list1)), 2):
        if [i2, i1] in used_indeces: continue
        used_indeces.append([i1, i2])
        perm_list_1.append([list1[i1], list1[i2]])
        perm_list_2.append([list2[i1], list2[i2]])
    return perm_list_1, perm_list_2

class FactorDB():
    
    def __init__(self, n):
        self.n = n
        self.ENDPOINT = "http://factordb.com/api"
        self.result = None

    def connect(self, reconnect=False):
        if self.result and not reconnect:
            return self.result
        self.result = requests.get(self.ENDPOINT, params={"query": str(self.n)})
        return self.result

    def get_id(self):
        if self.result:
            return self.result.json().get("id")
        return None

    def get_status(self):
        if self.result:
            return self.result.json().get("status")
        return None

    def get_factor_from_api(self):
        if self.result:
            return   self.result.json().get("factors") 
        return None

    def get_factor_list(self):
        """
        get_factors: [['2', 3], ['3', 2]]
        Returns: [2, 2, 2, 3, 3]
        """
        factors = self.get_factor_from_api()
        if not factors:
            return []
        ml = [[int(x)] * y for x, y in factors]
        return [y for x in ml for y in x]

def boneh_durfee_attack(n,e):
    debug = False
    strict = False
    helpful_only = True
    dimension_min = 7
    def helpful_vectors(BB, modulus):
        nothelpful = 0
        for ii in range(BB.dimensions()[0]):
            if BB[ii,ii] >= modulus:
                nothelpful += 1
    def matrix_overview(BB, bound):
        for ii in range(BB.dimensions()[0]):
            a = ('%02d ' % ii)
            for jj in range(BB.dimensions()[1]):
                a += '0' if BB[ii,jj] == 0 else 'X'
                if BB.dimensions()[0] < 60:
                    a += ' '
            if BB[ii, ii] >= bound:
                a += '~'
    def remove_unhelpful(BB, monomials, bound, current):
        if current == -1 or BB.dimensions()[0] <= dimension_min:
            return BB
        for ii in range(current, -1, -1):
            if BB[ii, ii] >= bound:
                affected_vectors = 0
                affected_vector_index = 0
                for jj in range(ii + 1, BB.dimensions()[0]):
                    if BB[jj, ii] != 0:
                        affected_vectors += 1
                        affected_vector_index = jj
                if affected_vectors == 0:
                    BB = BB.delete_columns([ii])
                    BB = BB.delete_rows([ii])
                    monomials.pop(ii)
                    BB = remove_unhelpful(BB, monomials, bound, ii-1)
                    return BB
                elif affected_vectors == 1:
                    affected_deeper = True
                    for kk in range(affected_vector_index + 1, BB.dimensions()[0]):
                        if BB[kk, affected_vector_index] != 0:
                            affected_deeper = False
                    if affected_deeper and abs(bound - BB[affected_vector_index, affected_vector_index]) < abs(bound - BB[ii, ii]):
                        BB = BB.delete_columns([affected_vector_index, ii])
                        BB = BB.delete_rows([affected_vector_index, ii])
                        monomials.pop(affected_vector_index)
                        monomials.pop(ii)
                        BB = remove_unhelpful(BB, monomials, bound, ii-1)
                        return BB
        return BB
    def boneh_durfee(pol, modulus, mm, tt, XX, YY):
        PR.<u, x, y> = PolynomialRing(ZZ)
        Q = PR.quotient(x*y + 1 - u)
        polZ = Q(pol).lift()
        UU = XX*YY + 1
        gg = []
        for kk in range(mm + 1):
            for ii in range(mm - kk + 1):
                xshift = x^ii * modulus^(mm - kk) * polZ(u, x, y)^kk
                gg.append(xshift)
        gg.sort()
        monomials = []
        for polynomial in gg:
            for monomial in polynomial.monomials():
                if monomial not in monomials:
                    monomials.append(monomial)
        monomials.sort()
        for jj in range(1, tt + 1):
            for kk in range(floor(mm/tt) * jj, mm + 1):
                yshift = y^jj * polZ(u, x, y)^kk * modulus^(mm - kk)
                yshift = Q(yshift).lift()
                gg.append(yshift)
        for jj in range(1, tt + 1):
            for kk in range(floor(mm/tt) * jj, mm + 1):
                monomials.append(u^kk * y^jj)
        nn = len(monomials)
        BB = Matrix(ZZ, nn)
        for ii in range(nn):
            BB[ii, 0] = gg[ii](0, 0, 0)
            for jj in range(1, ii + 1):
                if monomials[jj] in gg[ii].monomials():
                    BB[ii, jj] = gg[ii].monomial_coefficient(monomials[jj]) * monomials[jj](UU,XX,YY)
        if helpful_only:
            BB = remove_unhelpful(BB, monomials, modulus^mm, nn-1)
            nn = BB.dimensions()[0]
            if nn == 0:
                return 0,0
        if debug:
            helpful_vectors(BB, modulus^mm)
        det = BB.det()
        bound = modulus^(mm*nn)
        if det >= bound:
            if debug:
                diff = (log(det) - log(bound)) / log(2)
                print "size det(L) - size e^(m*n) = ", floor(diff)
            if strict:
                return -1, -1
        if debug:
            matrix_overview(BB, modulus^mm)
        BB = BB.LLL()
        PR.<w,z> = PolynomialRing(ZZ)
        pol1 = pol2 = 0
        for jj in range(nn):
            pol1 += monomials[jj](w*z+1,w,z) * BB[0, jj] / monomials[jj](UU,XX,YY)
            pol2 += monomials[jj](w*z+1,w,z) * BB[1, jj] / monomials[jj](UU,XX,YY)
        PR.<q> = PolynomialRing(ZZ)
        rr = pol1.resultant(pol2)
        if rr.is_zero() or rr.monomials() == [1]:
            return 0, 0
        rr = rr(q, q)
        soly = rr.roots()
        if len(soly) == 0:
            return 0, 0
        soly = soly[0][0]
        ss = pol1(q, soly)
        solx = ss.roots()[0][0]
        return solx, soly
    def start(N,e):
        delta = 0.292
        m = 4
        t = int((1-2*delta) * m)
        X = 2*floor(N^delta)
        Y = floor(N^(1/2))
        P.<x,y> = PolynomialRing(ZZ)
        A = int((N+1)/2)
        pol = 1 + x * (A + y)
        if debug:
            print "=== checking values ==="
            print "* delta:", delta
            print "* delta <= 0.292", delta <= 0.292
            print "* size of e:", int(log(e)/log(2))
            print "* size of N:", int(log(N)/log(2))
            print "* m:", m, ", t:", t
        if debug:
            print "=== running algorithm ==="
            start_time = time.time()
        solx, soly = boneh_durfee(pol, e, m, t, X, Y)
        if solx > 0:
            if debug:
                print "x:", solx
                print "y:", soly
            d = int(pol(solx, soly) / e)
            return d
        else:
            return 0
        if debug:
            print("=== %s seconds ===" % (time.time() - start_time))
    return start(n,e)

def factorization(n,e,c,start=False):
    if start:
        print("[!] Starting the factorization module ...")
        print("[!] Use ctrl+c to continue to the next iteration/method")
    def primes_from_n_e_d(n,e,d):
        primes = []
        key = _slowmath.rsa_construct(long(n), long(e), long(d))
        p,q = key.p,key.q
        if is_prime(p): primes.append(p)
        else: primes += primes_from_n_e_d(p,e,d)
        if is_prime(q): primes.append(q)
        else: primes += primes_from_n_e_d(q,e,d)
        return primes
    if n <= 1: return []
    if is_prime(n): return [n]
    if is_even(n): return [2] + factorization(int(n/2),e,c)
    else:
        try:
            print("[!] Using factordb api ...")
            f = FactorDB(n)
            f.connect()
            if f.get_status() == 'FF':
                return f.get_factor_list()
        except requests.exceptions.RequestException: print("[-] Couldn't connect to factordb.com")
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using known-primes ...")
            for known_prime in known_primes:
                try: known_prime = long(known_prime)
                except: continue
                if n % known_prime == 0:
                    print("[!] Found one prime ... Getting the other(s)")
                    return factorization(known_prime,e,c) + factorization(int(n/known_prime),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using wiener attack ...")
            primes = []
            cf = convergents(e/n)
            for index, k in enumerate(cf[1:]):
                d, k = k.denominator(), k.numerator()
                if k != 0 and (e * d - 1) % k == 0:
                    phi = (e*d - 1) // k
                    if d == inverse_mod(e,phi) and pow(pow(2,e,n),d,n) == 2: return primes_from_n_e_d(n,e,d)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using common_factor_c_n method ...")
            if c > 0:
                common_factor = gcd(n, c)
                if common_factor > 1: return factorization(common_factor,e,c) + factorization(int(n/common_factor),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using common_factor_e_n method ...")
            if e > 0:
                common_factor = gcd(n, e)
                if common_factor > 1: return factorization(common_factor,e,c) + factorization(int(n/common_factor),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using smallq method ...")
            for q in all_primes(10000000):
                if n % q == 0:
                    return [q] + factorization(int(n/q),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using fermat attack ...")
            a = ceil(sqrt(n))
            i = 0
            while not is_square(a^2-n):
                if i==1000000: break
                a += 1
                i += 1
            if i != 1000000:
                b = sqrt(a^2-n)
                return factorization(a - b,e,c)+factorization(a + b,e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using smallfraction method ...")
            depth=50
            t = len(bin(n).replace('0b',''))
            nn = RealField(2000)(n)
            p = 0
            x = PolynomialRing(Zmod(n),"x").gen()
            for den in xrange(2,depth+1):
                for num in xrange(1,den):
                    if gcd(num,den)==1:
                        r=Integer(den)/Integer(num); 
                        phint = int(sqrt(nn*r))
                        f = x - phint
                        sr = f.small_roots(beta=0.5)
                        if len(sr) > 0:
                            p = int(phint - sr[0])
                            if n%p==0:
                                return factorization(p,e,c) + factorization(int(n/p),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using boneh_durfee attack [no multi-prime support] ...")
            d = boneh_durfee_attack(n,e)
            if d != 0: return primes_from_n_e_d(n,e,d)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using online magma calculator ...")
            primes = []
            answer = requests.post('https://magma.maths.usyd.edu.au/xml/calculator.xml',data={'input':'Factorization({})'.format(n)}).text
            query = re.compile("&lt;(.*?)&gt;")
            answer = query.findall(answer)
            possibles = [str(ii) for ii in range(10)] + [',']
            for item in answer:
                pair = ""
                for i in item: 
                    if i in possibles: pair += i
                pair = pair.split(",")
                for i in range(int(pair[1])):
                    primes.append(int(pair[0]))
            if len(primes) != 0: return primes
        except requests.exceptions.RequestException: print("[-] Couldn't connect to magma.maths.usyd.edu.au")
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using yafu ...")
            threads = multiprocessing.cpu_count()
            if not os.path.isdir("C:/"): binary = "yafu/yafu"
            else:
                if os.path.isdir("C:/Program Files (x86)"): binary = "yafu/yafu64.exe"
                else: binary = "yafu/yafu32.exe"
            result = subprocess.check_output([binary, 'factor('+str(n)+')' ,'-one' ,'-plan' ,'deep' ,'-p' ,'-threads', str(threads)])
            primes = []
            for line in result.splitlines():
                if re.search(b'^P[0-9]+\ =\ [0-9]+$', line):
                    primes.append(int(line.split(b'=')[1]))
            return primes + factorization(int(n/product(primes)),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using msieve ...")
            if not os.path.isdir("C:/"): raise Exception("[-] Msieve linux binary is not availible")
            else: binary = "msieve/msieve.exe"
            result = subprocess.check_output([binary, '-p' ,'-q' , str(n)])
            primes = []
            for line in result.splitlines():
                if re.search(b'^p[0-9]+:\ [0-9]+$', line):
                    primes.append(int(line.split(b':')[1]))
            return primes + factorization(int(n/product(primes)),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        print("[!] Using sagemath factorization functions ...")
        try:
            print("[!] Using factor ...")
            primes = []
            factors = list(factor(n))
            for pair in factors:
                for i in range(pair[1]):
                    primes.append(pair[0])
            return primes
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            if len(str(n)) >= 40:
                print("[!] Using qsieve ...")
                qfactors = qsieve(n)[0]
                length = len(qfactors)
                if length % 2 == 0: mid_factor = qfactors[(length/2)-1]
                else: mid_factor = qfactors[(length-1)/2]
                return factorization(mid_factor,e,c) + factorization(int(n/mid_factor),e,c)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using ecm ...")
            return ecm.factor(n)
        except Exception as err: print("[-] " + str(err))
        except: pass
        try:
            print("[!] Using primefac lib ...")
            print("[!] high cpu usage ...")
            return list(primefac(n, methods=(pollardRho_brent, pollard_pm1, williams_pp1)))
        except Exception as err: print("[-] " + str(err))
        except: pass
        return []

def factorise(n,e=0,c=0):
    global known_primes
    if not os.path.isfile("known_primes.txt"): open("known_primes.txt",'w').close()
    known_primes = open("known_primes.txt",'r').read().splitlines()
    primes = factorization(n,e,c,True)
    if product(primes) == n:
        known_primes = open("known_primes.txt",'r').read().strip().splitlines()
        with open("known_primes.txt","ab") as file:
            for prime in list(set(primes)): 
                if not str(prime) in known_primes: file.write("\n"+str(prime))
        return primes
    return []

def simple_decryption(n=0,d=0,e=0,c=0,primes=[],d_primes=[]):
    try:
        if n != 0 and d != 0 and c != 0: return pow(c,d,n)
        elif d != 0 and c != 0 and primes != []: return pow(c,d,clc_n_phi(primes)[0])
        elif e != 0 and c != 0 and primes != []: n,phi = clc_n_phi(primes); return pow(c,inverse_mod(e,phi),n)
        elif primes != [] and d_primes != [] and c != 0: d = crt(d_primes,[prime - 1 for prime in primes]); return pow(c,d,clc_n_phi(primes)[0])
        elif c == 0: print("[-] This function needs a cipher to decrypt")
        else: print("[-] The given set of data is not enough to decrypt c")
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def simple_padded_m_brute_force(m,i=1,r=0):
    # m = (i^k) * m0 + r
    k = 0
    m0 = m - r
    ret = []
    while True:
        if m0 % pow(2,k) == 0: ret.append(m0/pow(2,k))
        else: break
        k+=1
    print("[!] It might be one of (specially the first ones): ")
    print(ret[::-1])


def e_equals_2_decryption(c,p,q):
    try:
        print("[!] Using Rabin Cryptosystem decryption [no multi prime support]")
        if p == q: return
        n = p * q
        inv_p = inverse_mod(p, q)
        inv_q = inverse_mod(q, p)
        mp = pow (c ,(p+1)/4 ,p) 
        mq = pow (c ,(q+1)/4 ,q)
        a = (inv_p*p*mq+inv_q*q*mp)%n
        b = n-int(a)
        c = (inv_p*p*mq-inv_q*q*mp)%n
        d = n-int(c)
        print("[!] The plaintext is one of four possibilties")
        return [a,b,c,d]
    except Exception as err: print("[-] " + str(err))
    except: pass
    return [0,0,0,0]

def small_e_brute_force(n,e,c):
    try:
        c0 = c
        while True:
            m = int(Integer(c)^(1/e))
            if pow(m, e, n) == c0: return m
            c += n
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def n_is_prime_attack(n,e,c):
    try:
        if not is_prime(n): return 0
        phi = clc_n_phi([n])[1]
        d = inverse_mod(e,phi)
        return pow(c,d,n)
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def common_e(n_list,e,c_list):
    if len(n_list) != len(c_list) or len(n_list) < 2 : print("[-] Two lists should have the same length with length > 1"); return
    print("[!] Trying Hastad Broadcast Attack")
    try: return crt(c_list,n_list).nth_root(e)
    except: pass
    print("[!] Trying Common Prime Attack")
    try:
        perms = two_lists_permutations(n_list,c_list)
        all_n, all_c = perms[0], perms[1]
        for i in range(len(all_n)):
            n1, n2 = all_n[i]
            c1, c2 = all_c[i]
            factor = gcd(n1,n2)
            if factor > 1:
                primes = factorise(factor) + factorise(n1/factor)
                c = c1
                if len(primes) < 2: primes = factorise(factor) + factorise(n2/factor); c = c2
                if len(primes) >= 2:
                    phi = clc_n_phi(primes)[1]
                    d = inverse_mod(e,phi)
                    return pow(c,d,n)
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def common_n(n,e_list,c_list):
    if len(e_list) != len(c_list) or len(e_list) < 2 : print("[-] Two lists should have the same length with length > 1"); return
    print("[!] Trying Common Modulus Attack")
    try:
        perms = two_lists_permutations(e_list,c_list)
        all_e, all_c = perms[0], perms[1]
        for i in range(len(all_e)):
            e1, e2 = all_e[i]
            c1, c2 = all_c[i]
            d, a, b = xgcd(e1,e2)
            if gcd(e1/d,e2/d) != 1: continue
            c3, c4 = c1, c2
            if b < 0: c4 = inverse_mod(c2, n); b = -b
            if a < 0: c3 = inverse_mod(c1, n); a = -a
            m = Integer((pow(c3,a,n) * pow(c4,b,n)) % n)
            return m.nth_root(d)
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def common_c(n_list,e_list,c):
    if len(n_list) != len(e_list) or len(n_list) < 2 : print("[-] Two lists should have the same length with length > 1"); return
    print("[!] Trying Common Prime Attack")
    try:
        perms = two_lists_permutations(n_list,e_list)
        all_n, all_e = perms[0], perms[1]
        for i in range(len(all_n)):
            n1, n2 = all_n[i]
            e1, e2 = all_e[i]
            factor = gcd(n1,n2)
            if factor > 1:
                primes = factorise(factor) + factorise(n1/factor)
                e = e1
                if len(primes) < 2: primes = factorise(factor) + factorise(n2/factor); e = e2
                if len(primes) >= 2:
                    phi = clc_n_phi(primes)[1]
                    d = inverse_mod(e,phi)
                    return pow(c,d,n)
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def related_m(n,e,c_list,r_list=[],eps=1/30):
    def composite_gcd(g1,g2): return g1.monic() if g2 == 0 else composite_gcd(g2, g1 % g2)
    def franklinReiter(n,e,c1,c2,r1,r2):
        R.<X> = Zmod(n)[]
        f1 = (X + r1)^e - c1
        f2 = (X + r2)^e - c2
        return Integer(n-(composite_gcd(f1,f2)).coefficients()[0])
    try:
        if r_list != []:
            # When there are m1, m2 and m1 = m0 + r1, m2 = m0 + r2 so as to get m0
            print("[!] Trying Franklin Reiter Related Message Attack ...")
            if len(c_list) == len(r_list) and len(c_list) >= 2 : 
                perms = two_lists_permutations(c_list,r_list)
                all_c, all_r = perms[0], perms[1]
                for i in range(len(all_c)):
                    c1, c2 = all_c[i]
                    r1, r2 = all_r[i]
                    m = franklinReiter(n,e,c1,c2,r1,r2)
                    if m != 0: return m
            else:
                print("[-] To use this attack the two lists should have the same length with length > 1")
        else:
            # When there are m1, m2 and m1 = (i^k)*m0 + r1, m2 = (i^k)*m0 + r2 so as to get m0
            print("[!] Trying Coppersmith ShortPad Attack ...")
            for C1,C2 in itertools.permutations(c_list, 2):
                P.<x,y> = PolynomialRing(ZZ)
                ZmodN = Zmod(n)
                g1 = x^e - C1
                g2 = (x+y)^e - C2
                res = g1.resultant(g2)
                P.<y> = PolynomialRing(ZmodN)
                rres = 0
                for i in range(len(res.coefficients())): rres += res.coefficients()[i]*(y^(res.exponents()[i][1]))
                diff = rres.small_roots(epsilon=eps)
                recoveredM1 = franklinReiter(n,e,C1,C2,0,diff[0])
                if recoveredM1 == 0: continue
                print("[!] The plaintext may be part of one of 8 possibilties")
                return [Integer(recoveredM1*pow(2,i)) for i in range(8)]
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def linear_padding_hastad_attack(c_list, n_list, pad_list, const_list, e, eps=1/8):
    # when ci = ((padi * m0 + ri) ^ e) % ni
    try:
        if not(len(c_list) == len(n_list) == len(pad_list) == len(const_list)) or len(c_list) < 2: print("[-] Four lists should have the same length with length > 1"); return
        T_array = [Integer(0)]*len(c_list)
        crt_array = [Integer(0)]*len(c_list)
        polynomial_array = []
        for i in range(len(c_list)):
            crt_array = [0]*len(c_list)
            crt_array[i] = 1
            try: T_array[i] = Integer(crt(crt_array,n_list))
            except: return 0
        G.<x> = PolynomialRing(Zmod(prod(n_list)))
        for i in range(len(c_list)):
            polynomial_array += [T_array[i]*((pad_list[i]*x+const_list[i])^e - Integer(c_list[i]))]
        g = sum(polynomial_array).monic()
        roots = g.small_roots(epsilon=eps)
        return roots[0] if len(roots) >= 1 else 0
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def chosen_ciphertext_attack(n, e, c):
    # when there's a decryption mechanism on a server and it decrypts any arbitrary cipher
    # The attacker has c,n,e
    # The attacker chooses c1 = c * pow(t,e,n) % n as t is a random number
    # Then he sends c1 to the server and gets m1
    # Then he gets the original m = m1 / t
    try:
        t = random.randint(1,n)
        c1 = c * pow(t,e,n) % n
        print("[!] Send this to the server: "+str(c1))
        m1 = int(input("[!] The response: "))
        print("[!] The Original message is: "+str(int(m1/t)))
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def partial_d(n,e,c,partial_d,kbits):
    # when partial_d = d & (2^kbits-1)
    def partial_p(p0, kbits, n):
        PR.<x> = PolynomialRing(Zmod(n))
        nbits = n.nbits()
        f = 2^kbits*x + p0
        f = f.monic()
        roots = f.small_roots(X=2^(nbits//2-kbits), beta=0.3)
        if roots:
            x0 = roots[0]
            p = gcd(2^kbits*x0 + p0, n)
            return ZZ(p)
    def find_p(d0, kbits, e, n):
        X = var('X')
        for k in xrange(1, e+1):
            results = solve_mod([e*d0*X - k*X*(n-X+1) + k*n == X], 2^kbits)
            for x in results:
                p0 = ZZ(x[0])
                p = partial_p(p0, kbits, n)
                if p:
                    return p
    try:
        p = find_p(partial_d, kbits, e, n)
        primes = factorise(p) + factorise(n/p)
        phi = clc_n_phi(primes)[1]
        d = inverse_mod(e, phi)
        return pow(c,d,n)
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def partial_m(n,e,c,partial_m,kbits):
    # when partial_m = m & (2^nbits-2^kbits) as nbits is bit length of n
    try:
        PR.<x> = PolynomialRing(Zmod(n))
        f = (partial_m + x)^e - c
        print partial_m + f.small_roots(X=2^kbits, beta=1)[0]
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def partial_p(n,e,c,partial_p,kbits):
    # when partial_p = p & (2^pbits-2^kbits) as pbits is bit length of p
    try:
        PR.<x> = PolynomialRing(Zmod(n))
        f = x + pbar
        p = partial_p + f.small_roots(X=2^kbits, beta=0.3)[0]
        primes = factorise(p) + factorise(n/p)
        phi = clc_n_phi(primes)[1]
        d = inverse_mod(e, phi)
        return pow(c,d,n)
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def partial_m_simple(n,e,c,partial_m,eps=1/8):
    # when m = m0 + partial_m and m0 < n
    # Actually you can perform this for any arithmatic operation on m
    # Just change the equation below
    try:
        ZmodN = Zmod(n)
        C = ZmodN(c)
        partial_m = ZmodN(partial_m)
        P.<x> = PolynomialRing(ZmodN)
        pol = (partial_m+x)^e - C
        diff = pol.small_roots(epsilon=eps)
        if(len(diff)==0): return 0
        return partial_m + diff[0]
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def known_Message_Format_attack(n,e,c,message,special_char='X',eps=1/15):
    # When the part of message is missing like
    # message = "flag is: {blah_blah_blahXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX}"
    # the XXXX.. is just the missing part
    # unknownEndBitIndex is the index of the start of missing part from the end
    try:
        message = message.replace(special_char,'\x00')
        unknownEndBitIndex = Integer(8*(len(message)-message.rfind('\x00')-1))
        message = int(message.encode('hex'),16)
        ZmodN = Zmod(n)
        c = ZmodN(c)
        e = ZmodN(e)
        message = ZmodN(message)
        P.<x> = PolynomialRing(ZmodN)
        pol = ((message + ZmodN((pow(2,unknownEndBitIndex)))*x)^e) - c
        pol = pol.monic()
        xval = pol.small_roots(epsilon=eps)
        if(len(xval)==0): return 0
        xval = xval[0]
        xval = xval*(2**unknownEndBitIndex)
        return Integer(message+xval)
    except Exception as err: print("[-] " + str(err))
    except: pass
    return 0

def partial_q_crt(e, c, dp, dq, qinv, part_q):
        # Like q = "ee145596a50e5699874421c1c65577" and partial_q is "4421c1c65577"
        for j in range(1000000, 1, -1):
            q = Integer(int((e * dq - 1) / j + 1))
            if str(hex(q)).strip('L').endswith(part_q): break
        for k in range(1, 1000000, 1):
            p = Integer(int((e * dp - 1) / k + 1))
            try:
                if inverse_mod(q, p) == qinv: break
            except: pass
        primes = factorise(p) + factorise(q)
        n,phi = clc_n_phi(primes)
        d = inverse_mod(e,phi)
        return pow(c,d,n)
