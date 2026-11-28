import OMAStatements.S_oeis_a359984

-- Problem: A359984: Number of non-crossing antichain covers of {1,...,n} without singletons.
-- Upstream: formal-conjectures statements/oeis-a359984.lean:0 (declaration OMA.S_oeis_a359984.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A359984Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-1 - 7 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (8 * X ^ 2 - 224 * X ^ 3 + 404 * X ^ 4 + 12400 * X ^ 5 + 53970 * X ^ 6 + 125498 * X ^ 7 + 121577 * X ^ 8 + 38285 * X ^ 9) * derivative ℚ (derivative ℚ G) + (132 * X ^ 2 - 708 * X ^ 3 - 9006 * X ^ 4 + 17618 * X ^ 5 + 122748 * X ^ 6 + 304860 * X ^ 7 + 153140 * X ^ 8) * derivative ℚ G + (144 * X ^ 2 + 444 * X ^ 3 - 24972 * X ^ 4 + 17428 * X ^ 5 + 61706 * X ^ 6 + 76570 * X ^ 7) * G =
      160 * X ^ 2 + 500 * X ^ 3 - 26336 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have hp0 : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-1 - 7 * X - 3 * (X * X) : ℚ⟦X⟧) * G * G + (1 + 3 * X + 3 * (X * X) + 1 * (X * X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-1 - 7 * X - 3 * (X * X) : ℚ⟦X⟧) * G * G + (1 + 3 * X + 3 * (X * X) + 1 * (X * X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-7 - 6 * X : ℚ⟦X⟧) * G ^ 2 + (3 + 9 * X + 9 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (3 + 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d3, d4, d7]
    ring
  have hd1 : (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-7 - 6 * X : ℚ⟦X⟧) * G ^ 2 + (3 + 9 * X + 9 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (3 + 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-2 - 14 * X - 6 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-7 - 6 * X : ℚ⟦X⟧) * G * G + (3 + 9 * X + 9 * (X * X) + 3 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (3 + 6 * X + 3 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-2 - 14 * X - 6 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-7 - 6 * X : ℚ⟦X⟧) * G * G + (3 + 9 * X + 9 * (X * X) + 3 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (3 + 6 * X + 3 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-28 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 + 18 * X + 18 * X ^ 2 + 6 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 + (3 + 9 * X + 9 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (18 + 36 * X + 18 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 + 6 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d7, d9, d14]
    ring
  have hd2 : (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-28 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 + 18 * X + 18 * X ^ 2 + 6 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 + (3 + 9 * X + 9 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (18 + 36 * X + 18 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 + 6 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 + 4 * X : ℚ⟦X⟧) + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G + (3 + 9 * X + 9 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((8 * X ^ 2 - 224 * X ^ 3 + 404 * X ^ 4 + 12400 * X ^ 5 + 53970 * X ^ 6 + 125498 * X ^ 7 + 121577 * X ^ 8 + 38285 * X ^ 9) * derivative ℚ (derivative ℚ G) + (132 * X ^ 2 - 708 * X ^ 3 - 9006 * X ^ 4 + 17618 * X ^ 5 + 122748 * X ^ 6 + 304860 * X ^ 7 + 153140 * X ^ 8) * derivative ℚ G + (144 * X ^ 2 + 444 * X ^ 3 - 24972 * X ^ 4 + 17428 * X ^ 5 + 61706 * X ^ 6 + 76570 * X ^ 7) * G - (160 * X ^ 2 + 500 * X ^ 3 - 26336 * X ^ 4)) = 0 := by
    linear_combination ((160 * X ^ 2 - 1420 * X ^ 3 - 24656 * X ^ 4 + 329792 * X ^ 5 - 1296128 * X ^ 6 + 1685504 * X ^ 7 : ℚ⟦X⟧) + (192 * X ^ 2 + 16512 * X ^ 3 - 228804 * X ^ 4 - 427716 * X ^ 5 + 5425206 * X ^ 6 - 4189074 * X ^ 7 - 1794072 * X ^ 8 : ℚ⟦X⟧) * G + (-84 * X ^ 2 - 3228 * X ^ 3 + 307914 * X ^ 4 - 2297970 * X ^ 5 - 10126254 * X ^ 6 + 3812694 * X ^ 7 + 11015850 * X ^ 8 + 4487610 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (-1008 * X ^ 2 - 39024 * X ^ 3 + 225288 * X ^ 4 + 4123584 * X ^ 5 + 7902288 * X ^ 6 - 5580576 * X ^ 7 - 24133392 * X ^ 8 - 18916992 * X ^ 9 - 4406184 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (756 * X ^ 2 + 26244 * X ^ 3 - 264870 * X ^ 4 - 1735668 * X ^ 5 - 2738124 * X ^ 6 + 1332126 * X ^ 7 + 8672994 * X ^ 8 + 10410120 * X ^ 9 + 5463612 * X ^ 10 + 1101546 * X ^ 11 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((196 * X ^ 2 - 3812 * X ^ 3 + 9170 * X ^ 4 + 164610 * X ^ 5 - 127332 * X ^ 6 - 1118292 * X ^ 7 - 3365092 * X ^ 8 + 68456 * X ^ 9 + 1225120 * X ^ 10 : ℚ⟦X⟧) + (-16 * X ^ 2 + 400 * X ^ 3 + 936 * X ^ 4 - 38232 * X ^ 5 - 167516 * X ^ 6 + 54880 * X ^ 7 + 1999958 * X ^ 8 + 6764148 * X ^ 9 + 8861092 * X ^ 10 + 4832098 * X ^ 11 + 918840 * X ^ 12 : ℚ⟦X⟧) * (derivative ℚ G) + (368 * X ^ 2 + 4384 * X ^ 3 - 97096 * X ^ 4 - 189840 * X ^ 5 + 2391672 * X ^ 6 + 8112624 * X ^ 7 + 13266988 * X ^ 8 - 2739076 * X ^ 9 - 9845000 * X ^ 10 - 2756520 * X ^ 11 : ℚ⟦X⟧) * G + (16 * X ^ 2 - 944 * X ^ 3 + 12504 * X ^ 4 + 59256 * X ^ 5 - 719620 * X ^ 6 - 6573840 * X ^ 7 - 25251342 * X ^ 8 - 55220636 * X ^ 9 - 68290500 * X ^ 10 - 46468988 * X ^ 11 - 16253310 * X ^ 12 - 2297100 * X ^ 13 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-456 * X ^ 2 + 12048 * X ^ 3 + 78540 * X ^ 4 - 1090720 * X ^ 5 - 7775552 * X ^ 6 - 19409188 * X ^ 7 - 22472752 * X ^ 8 + 4424818 * X ^ 9 + 22785722 * X ^ 10 + 12946860 * X ^ 11 + 2297100 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (144 * X ^ 2 - 2592 * X ^ 3 - 29160 * X ^ 4 + 191520 * X ^ 5 + 3277116 * X ^ 6 + 18161316 * X ^ 7 + 58030902 * X ^ 8 + 117273294 * X ^ 9 + 152218566 * X ^ 10 + 125504280 * X ^ 11 + 63154098 * X ^ 12 + 17591238 * X ^ 13 + 2067390 * X ^ 14 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-1008 * X ^ 2 - 20016 * X ^ 3 + 88776 * X ^ 4 + 1947864 * X ^ 5 + 9004224 * X ^ 6 + 21523536 * X ^ 7 + 28497876 * X ^ 8 + 17247300 * X ^ 9 - 2018286 * X ^ 10 - 8823210 * X ^ 11 - 4385238 * X ^ 12 - 689130 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 + (-144 * X ^ 2 + 3168 * X ^ 3 + 14760 * X ^ 4 - 209232 * X ^ 5 - 2341260 * X ^ 6 - 11521548 * X ^ 7 - 34863102 * X ^ 8 - 70520706 * X ^ 9 - 98058222 * X ^ 10 - 94041090 * X ^ 11 - 61133634 * X ^ 12 - 25726230 * X ^ 13 - 6323166 * X ^ 14 - 689130 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (900 * X ^ 2 + 7380 * X ^ 3 - 78570 * X ^ 4 - 840942 * X ^ 5 - 3510486 * X ^ 6 - 8760906 * X ^ 7 - 14594202 * X ^ 8 - 16711110 * X ^ 9 - 13009302 * X ^ 10 - 6574626 * X ^ 11 - 1943316 * X ^ 12 - 254772 * X ^ 13 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((8 * X ^ 2 - 288 * X ^ 3 + 2324 * X ^ 4 + 5584 * X ^ 5 - 38766 * X ^ 6 - 107862 * X ^ 7 - 18887 * X ^ 8 + 1073637 * X ^ 9 + 1638952 * X ^ 10 + 612560 * X ^ 11 : ℚ⟦X⟧) + (32 * X ^ 2 - 800 * X ^ 3 - 1872 * X ^ 4 + 76464 * X ^ 5 + 335032 * X ^ 6 - 109760 * X ^ 7 - 3999916 * X ^ 8 - 13528296 * X ^ 9 - 17722184 * X ^ 10 - 9664196 * X ^ 11 - 1837680 * X ^ 12 : ℚ⟦X⟧) * G + (-16 * X ^ 2 + 944 * X ^ 3 - 12504 * X ^ 4 - 59256 * X ^ 5 + 719620 * X ^ 6 + 6573840 * X ^ 7 + 25251342 * X ^ 8 + 55220636 * X ^ 9 + 68290500 * X ^ 10 + 46468988 * X ^ 11 + 16253310 * X ^ 12 + 2297100 * X ^ 13 : ℚ⟦X⟧) * G ^ 2 + (-96 * X ^ 2 + 1728 * X ^ 3 + 19440 * X ^ 4 - 127680 * X ^ 5 - 2184744 * X ^ 6 - 12107544 * X ^ 7 - 38687268 * X ^ 8 - 78182196 * X ^ 9 - 101479044 * X ^ 10 - 83669520 * X ^ 11 - 42102732 * X ^ 12 - 11727492 * X ^ 13 - 1378260 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 + (72 * X ^ 2 - 1584 * X ^ 3 - 7380 * X ^ 4 + 104616 * X ^ 5 + 1170630 * X ^ 6 + 5760774 * X ^ 7 + 17431551 * X ^ 8 + 35260353 * X ^ 9 + 49029111 * X ^ 10 + 47020545 * X ^ 11 + 30566817 * X ^ 12 + 12863115 * X ^ 13 + 3161583 * X ^ 14 + 344565 * X ^ 15 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hres : ((72 + 180 * X + 540 * X ^ 2 + 135 * X ^ 3 + 441 * X ^ 4 + 333 * X ^ 5 : ℚ⟦X⟧) + (270 * X + 774 * X ^ 2 + 1971 * X ^ 3 + 405 * X ^ 4 - 927 * X ^ 5 - 351 * X ^ 6 : ℚ⟦X⟧) * G + (-72 - 414 * X - 1314 * X ^ 2 - 2340 * X ^ 3 - 2142 * X ^ 4 - 828 * X ^ 5 + 54 * X ^ 7 : ℚ⟦X⟧) * G ^ 2) * ((-1 + 4 * X : ℚ⟦X⟧) + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G + (3 + 9 * X + 9 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) = (-36 * X ^ 2 + 396 * X ^ 3 + 1476 * X ^ 4 + 4320 * X ^ 5 + 2223 * X ^ 6 : ℚ⟦X⟧) := by
    linear_combination (-((72 - 108 * X - 216 * X ^ 2 - 1629 * X ^ 3 + 1377 * X ^ 4 + 2889 * X ^ 5 + 891 * X ^ 6 : ℚ⟦X⟧) + (216 + 1242 * X + 3942 * X ^ 2 + 7020 * X ^ 3 + 6426 * X ^ 4 + 2484 * X ^ 5 - 162 * X ^ 7 : ℚ⟦X⟧) * G)) * hP
  have hd0 : (-36 + 396 * X + 1476 * X ^ 2 + 4320 * X ^ 3 + 2223 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (36 : ℚ⟦X⟧) = 36 := cnum 36
    simp [kc] at h'
  have hdisc : (-36 * X ^ 2 + 396 * X ^ 3 + 1476 * X ^ 4 + 4320 * X ^ 5 + 2223 * X ^ 6 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-36 * X ^ 2 + 396 * X ^ 3 + 1476 * X ^ 4 + 4320 * X ^ 5 + 2223 * X ^ 6 : ℚ⟦X⟧) = X ^ 2 * (-36 + 396 * X + 1476 * X ^ 2 + 4320 * X ^ 3 + 2223 * X ^ 4 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) hd0
  have hPG : (-1 + 4 * X : ℚ⟦X⟧) + (-2 - 14 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G + (3 + 9 * X + 9 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-1 - 7 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    derivative ℚ (derivative ℚ G) * X * X * C 8 + derivative ℚ (derivative ℚ G) * X * X * X * C (-224) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 404 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 12400 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 53970 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 125498 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 121577 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * C 38285 +
      derivative ℚ G * X * X * C 132 + derivative ℚ G * X * X * X * C (-708) +
      derivative ℚ G * X * X * X * X * C (-9006) + derivative ℚ G * X * X * X * X * X * C 17618 +
      derivative ℚ G * X * X * X * X * X * X * C 122748 + derivative ℚ G * X * X * X * X * X * X * X * C 304860 +
      derivative ℚ G * X * X * X * X * X * X * X * X * C 153140 + G * X * X * C 144 +
      G * X * X * X * C 444 + G * X * X * X * X * C (-24972) +
      G * X * X * X * X * X * C 17428 + G * X * X * X * X * X * X * C 61706 +
      G * X * X * X * X * X * X * X * C 76570 =
      C 160 * X * X + C 500 * X * X * X +
      C (-26336) * X * X * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-1 - 7 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) (m : ℕ) :
    8 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-224) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      404 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 12400 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      53970 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 125498 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      121577 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 38285 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      132 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-708) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-9006) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 17618 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      122748 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 304860 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      153140 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 144 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      444 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-24972) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      17428 * coeff (m + 1 + 1 + 1 + 1) G + 61706 * coeff (m + 1 + 1 + 1) G +
      76570 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-1 - 7 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    336 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6720) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      8080 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 148800 * coeff (0 + 1 + 1 + 1 + 1) G +
      323820 * coeff (0 + 1 + 1 + 1) G + 250996 * coeff (0 + 1 + 1) G +
      792 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3540) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-36024) * coeff (0 + 1 + 1 + 1 + 1) G + 52854 * coeff (0 + 1 + 1 + 1) G +
      245496 * coeff (0 + 1 + 1) G + 304860 * coeff (0 + 1) G +
      144 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 444 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-24972) * coeff (0 + 1 + 1 + 1) G + 17428 * coeff (0 + 1 + 1) G +
      61706 * coeff (0 + 1) G + 76570 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-1 - 7 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 3 * X + 3 * X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    448 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-9408) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      12120 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 248000 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      647640 * coeff (0 + 1 + 1 + 1 + 1) G + 752988 * coeff (0 + 1 + 1 + 1) G +
      243154 * coeff (0 + 1 + 1) G + 924 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-4248) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-45030) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      70472 * coeff (0 + 1 + 1 + 1 + 1) G + 368244 * coeff (0 + 1 + 1 + 1) G +
      609720 * coeff (0 + 1 + 1) G + 153140 * coeff (0 + 1) G +
      144 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 444 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-24972) * coeff (0 + 1 + 1 + 1 + 1) G + 17428 * coeff (0 + 1 + 1 + 1) G +
      61706 * coeff (0 + 1 + 1) G + 76570 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A359984Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a359984.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  have hN1 : ((1) : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : (2187 * PowerSeries.X ^ 14 + 15309 * PowerSeries.X ^ 15 + 45927 * PowerSeries.X ^ 16 + 76545 * PowerSeries.X ^ 17 + 76545 * PowerSeries.X ^ 18 + 45927 * PowerSeries.X ^ 19 + 15309 * PowerSeries.X ^ 20 + 2187 * PowerSeries.X ^ 21 : PowerSeries ℚ) * (((1)) ^ 3 * ((1 : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G + (-1 - 7 * PowerSeries.X - 3 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 + 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3)) = 0 := by
    linear_combination ((-2187) * PowerSeries.X ^ 17 + (-2187) * PowerSeries.X ^ 17 * T + (-15309) * PowerSeries.X ^ 18 + (-15309) * PowerSeries.X ^ 18 * T + (2187) * PowerSeries.X ^ 18 * T ^ 2 + (4374) * PowerSeries.X ^ 18 * T ^ 3 + (-45927) * PowerSeries.X ^ 19 + (-45927) * PowerSeries.X ^ 19 * T + (10935) * PowerSeries.X ^ 19 * T ^ 2 + (41553) * PowerSeries.X ^ 19 * T ^ 3 + (-8748) * PowerSeries.X ^ 19 * T ^ 4 + (-76545) * PowerSeries.X ^ 20 + (-76545) * PowerSeries.X ^ 20 * T + (15309) * PowerSeries.X ^ 20 * T ^ 2 + (181521) * PowerSeries.X ^ 20 * T ^ 3 + (-52488) * PowerSeries.X ^ 20 * T ^ 4 + (-6561) * PowerSeries.X ^ 20 * T ^ 5 + (-76545) * PowerSeries.X ^ 21 + (-76545) * PowerSeries.X ^ 21 * T + (-15309) * PowerSeries.X ^ 21 * T ^ 2 + (474579) * PowerSeries.X ^ 21 * T ^ 3 + (-124659) * PowerSeries.X ^ 21 * T ^ 4 + (-39366) * PowerSeries.X ^ 21 * T ^ 5 + (-19683) * PowerSeries.X ^ 21 * T ^ 6 + (-45927) * PowerSeries.X ^ 22 + (-45927) * PowerSeries.X ^ 22 * T + (-76545) * PowerSeries.X ^ 22 * T ^ 2 + (811377) * PowerSeries.X ^ 22 * T ^ 3 + (-137781) * PowerSeries.X ^ 22 * T ^ 4 + (-78732) * PowerSeries.X ^ 22 * T ^ 5 + (-177147) * PowerSeries.X ^ 22 * T ^ 6 + (-15309) * PowerSeries.X ^ 23 + (-15309) * PowerSeries.X ^ 23 * T + (-107163) * PowerSeries.X ^ 23 * T ^ 2 + (933849) * PowerSeries.X ^ 23 * T ^ 3 + (-45927) * PowerSeries.X ^ 23 * T ^ 4 + (-708588) * PowerSeries.X ^ 23 * T ^ 6 + (-2187) * PowerSeries.X ^ 24 + (-2187) * PowerSeries.X ^ 24 * T + (-76545) * PowerSeries.X ^ 24 * T ^ 2 + (719523) * PowerSeries.X ^ 24 * T ^ 3 + (45927) * PowerSeries.X ^ 24 * T ^ 4 + (275562) * PowerSeries.X ^ 24 * T ^ 5 + (-1653372) * PowerSeries.X ^ 24 * T ^ 6 + (-28431) * PowerSeries.X ^ 25 * T ^ 2 + (356481) * PowerSeries.X ^ 25 * T ^ 3 + (45927) * PowerSeries.X ^ 25 * T ^ 4 + (551124) * PowerSeries.X ^ 25 * T ^ 5 + (-2480058) * PowerSeries.X ^ 25 * T ^ 6 + (-4374) * PowerSeries.X ^ 26 * T ^ 2 + (102789) * PowerSeries.X ^ 26 * T ^ 3 + (6561) * PowerSeries.X ^ 26 * T ^ 4 + (551124) * PowerSeries.X ^ 26 * T ^ 5 + (-2480058) * PowerSeries.X ^ 26 * T ^ 6 + (13122) * PowerSeries.X ^ 27 * T ^ 3 + (-6561) * PowerSeries.X ^ 27 * T ^ 4 + (314928) * PowerSeries.X ^ 27 * T ^ 5 + (-1653372) * PowerSeries.X ^ 27 * T ^ 6 + (-2187) * PowerSeries.X ^ 28 * T ^ 4 + (98415) * PowerSeries.X ^ 28 * T ^ 5 + (-708588) * PowerSeries.X ^ 28 * T ^ 6 + (13122) * PowerSeries.X ^ 29 * T ^ 5 + (-177147) * PowerSeries.X ^ 29 * T ^ 6 + (-19683) * PowerSeries.X ^ 30 * T ^ 6) * hT +
      ((-2187) * PowerSeries.X ^ 14 + (2187) * PowerSeries.X ^ 14 * G ^ 2 + (-15309) * PowerSeries.X ^ 15 + (-8748) * PowerSeries.X ^ 15 * G + (21870) * PowerSeries.X ^ 15 * G ^ 2 + (-45927) * PowerSeries.X ^ 16 + (2187) * PowerSeries.X ^ 16 * T ^ 2 + (-61236) * PowerSeries.X ^ 16 * G + (2187) * PowerSeries.X ^ 16 * G * T ^ 2 + (98415) * PowerSeries.X ^ 16 * G ^ 2 + (-74358) * PowerSeries.X ^ 17 + (13122) * PowerSeries.X ^ 17 * T ^ 2 + (-6561) * PowerSeries.X ^ 17 * T ^ 3 + (-181521) * PowerSeries.X ^ 17 * G + (21870) * PowerSeries.X ^ 17 * G * T ^ 2 + (-6561) * PowerSeries.X ^ 17 * G * T ^ 3 + (262440) * PowerSeries.X ^ 17 * G ^ 2 + (-61236) * PowerSeries.X ^ 18 + (37179) * PowerSeries.X ^ 18 * T ^ 2 + (-39366) * PowerSeries.X ^ 18 * T ^ 3 + (2187) * PowerSeries.X ^ 18 * T ^ 4 + (-290871) * PowerSeries.X ^ 18 * G + (98415) * PowerSeries.X ^ 18 * G * T ^ 2 + (-65610) * PowerSeries.X ^ 18 * G * T ^ 3 + (459270) * PowerSeries.X ^ 18 * G ^ 2 + (80919) * PowerSeries.X ^ 19 * T ^ 2 + (-111537) * PowerSeries.X ^ 19 * T ^ 3 + (21870) * PowerSeries.X ^ 19 * T ^ 4 + (-13122) * PowerSeries.X ^ 19 * T ^ 5 + (-260253) * PowerSeries.X ^ 19 * G + (262440) * PowerSeries.X ^ 19 * G * T ^ 2 + (-295245) * PowerSeries.X ^ 19 * G * T ^ 3 + (551124) * PowerSeries.X ^ 19 * G ^ 2 + (61236) * PowerSeries.X ^ 20 + (168399) * PowerSeries.X ^ 20 * T ^ 2 + (-242757) * PowerSeries.X ^ 20 * T ^ 3 + (98415) * PowerSeries.X ^ 20 * T ^ 4 + (-131220) * PowerSeries.X ^ 20 * T ^ 5 + (19683) * PowerSeries.X ^ 20 * T ^ 6 + (-107163) * PowerSeries.X ^ 20 * G + (459270) * PowerSeries.X ^ 20 * G * T ^ 2 + (-787320) * PowerSeries.X ^ 20 * G * T ^ 3 + (459270) * PowerSeries.X ^ 20 * G ^ 2 + (74358) * PowerSeries.X ^ 21 + (290871) * PowerSeries.X ^ 21 * T ^ 2 + (-505197) * PowerSeries.X ^ 21 * T ^ 3 + (262440) * PowerSeries.X ^ 21 * T ^ 4 + (-590490) * PowerSeries.X ^ 21 * T ^ 5 + (196830) * PowerSeries.X ^ 21 * T ^ 6 + (15309) * PowerSeries.X ^ 21 * G + (551124) * PowerSeries.X ^ 21 * G * T ^ 2 + (-1377810) * PowerSeries.X ^ 21 * G * T ^ 3 + (262440) * PowerSeries.X ^ 21 * G ^ 2 + (45927) * PowerSeries.X ^ 22 + (352107) * PowerSeries.X ^ 22 * T ^ 2 + (-872613) * PowerSeries.X ^ 22 * T ^ 3 + (459270) * PowerSeries.X ^ 22 * T ^ 4 + (-1574640) * PowerSeries.X ^ 22 * T ^ 5 + (885735) * PowerSeries.X ^ 22 * T ^ 6 + (37179) * PowerSeries.X ^ 22 * G + (459270) * PowerSeries.X ^ 22 * G * T ^ 2 + (-1653372) * PowerSeries.X ^ 22 * G * T ^ 3 + (98415) * PowerSeries.X ^ 22 * G ^ 2 + (15309) * PowerSeries.X ^ 23 + (277749) * PowerSeries.X ^ 23 * T ^ 2 + (-1056321) * PowerSeries.X ^ 23 * T ^ 3 + (551124) * PowerSeries.X ^ 23 * T ^ 4 + (-2755620) * PowerSeries.X ^ 23 * T ^ 5 + (2361960) * PowerSeries.X ^ 23 * T ^ 6 + (15309) * PowerSeries.X ^ 23 * G + (262440) * PowerSeries.X ^ 23 * G * T ^ 2 + (-1377810) * PowerSeries.X ^ 23 * G * T ^ 3 + (21870) * PowerSeries.X ^ 23 * G ^ 2 + (2187) * PowerSeries.X ^ 24 + (135594) * PowerSeries.X ^ 24 * T ^ 2 + (-833247) * PowerSeries.X ^ 24 * T ^ 3 + (459270) * PowerSeries.X ^ 24 * T ^ 4 + (-3306744) * PowerSeries.X ^ 24 * T ^ 5 + (4133430) * PowerSeries.X ^ 24 * T ^ 6 + (2187) * PowerSeries.X ^ 24 * G + (98415) * PowerSeries.X ^ 24 * G * T ^ 2 + (-787320) * PowerSeries.X ^ 24 * G * T ^ 3 + (2187) * PowerSeries.X ^ 24 * G ^ 2 + (37179) * PowerSeries.X ^ 25 * T ^ 2 + (-406782) * PowerSeries.X ^ 25 * T ^ 3 + (262440) * PowerSeries.X ^ 25 * T ^ 4 + (-2755620) * PowerSeries.X ^ 25 * T ^ 5 + (4960116) * PowerSeries.X ^ 25 * T ^ 6 + (21870) * PowerSeries.X ^ 25 * G * T ^ 2 + (-295245) * PowerSeries.X ^ 25 * G * T ^ 3 + (4374) * PowerSeries.X ^ 26 * T ^ 2 + (-111537) * PowerSeries.X ^ 26 * T ^ 3 + (98415) * PowerSeries.X ^ 26 * T ^ 4 + (-1574640) * PowerSeries.X ^ 26 * T ^ 5 + (4133430) * PowerSeries.X ^ 26 * T ^ 6 + (2187) * PowerSeries.X ^ 26 * G * T ^ 2 + (-65610) * PowerSeries.X ^ 26 * G * T ^ 3 + (-13122) * PowerSeries.X ^ 27 * T ^ 3 + (21870) * PowerSeries.X ^ 27 * T ^ 4 + (-590490) * PowerSeries.X ^ 27 * T ^ 5 + (2361960) * PowerSeries.X ^ 27 * T ^ 6 + (-6561) * PowerSeries.X ^ 27 * G * T ^ 3 + (2187) * PowerSeries.X ^ 28 * T ^ 4 + (-131220) * PowerSeries.X ^ 28 * T ^ 5 + (885735) * PowerSeries.X ^ 28 * T ^ 6 + (-13122) * PowerSeries.X ^ 29 * T ^ 5 + (196830) * PowerSeries.X ^ 29 * T ^ 6 + (19683) * PowerSeries.X ^ 30 * T ^ 6) * hG
  have hL0 : (2187 + 15309 * PowerSeries.X + 45927 * PowerSeries.X ^ 2 + 76545 * PowerSeries.X ^ 3 + 76545 * PowerSeries.X ^ 4 + 45927 * PowerSeries.X ^ 5 + 15309 * PowerSeries.X ^ 6 + 2187 * PowerSeries.X ^ 7 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (2187 : PowerSeries ℚ) = 2187 := A359984Aux.cnum 2187
    simp [kc] at h'
  have hLne : (2187 * PowerSeries.X ^ 14 + 15309 * PowerSeries.X ^ 15 + 45927 * PowerSeries.X ^ 16 + 76545 * PowerSeries.X ^ 17 + 76545 * PowerSeries.X ^ 18 + 45927 * PowerSeries.X ^ 19 + 15309 * PowerSeries.X ^ 20 + 2187 * PowerSeries.X ^ 21 : PowerSeries ℚ) ≠ 0 := by
    have e : (2187 * PowerSeries.X ^ 14 + 15309 * PowerSeries.X ^ 15 + 45927 * PowerSeries.X ^ 16 + 76545 * PowerSeries.X ^ 17 + 76545 * PowerSeries.X ^ 18 + 45927 * PowerSeries.X ^ 19 + 15309 * PowerSeries.X ^ 20 + 2187 * PowerSeries.X ^ 21 : PowerSeries ℚ) = PowerSeries.X ^ 14 * (2187 + 15309 * PowerSeries.X + 45927 * PowerSeries.X ^ 2 + 76545 * PowerSeries.X ^ 3 + 76545 * PowerSeries.X ^ 4 + 45927 * PowerSeries.X ^ 5 + 15309 * PowerSeries.X ^ 6 + 2187 * PowerSeries.X ^ 7 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 14 PowerSeries.X_ne_zero) hL0
  have hP : (1 : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G + (-1 - 7 * PowerSeries.X - 3 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 + 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 3 hN1)
  cases m with
  | zero =>
    have r := A359984Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A359984Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A359984Aux.rel G hP m
      push_cast
      linear_combination r
