import OMAStatements.S_oeis_a243764

-- Problem: A243764: Expansion of -((2*sqrt(1-4*x)-2)*x)/(sqrt(8*x+4*sqrt(1-4*x)-3)-1).
-- Upstream: formal-conjectures statements/oeis-a243764.lean:0 (declaration OMA.S_oeis_a243764.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A243764Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    (245 * X ^ 3 - 3920 * X ^ 4 + 23248 * X ^ 5 - 53888 * X ^ 6 - 19456 * X ^ 7 + 303104 * X ^ 8 - 393216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-420 * X ^ 3 - 3216 * X ^ 4 + 75648 * X ^ 5 - 390144 * X ^ 6 + 860160 * X ^ 7 - 786432 * X ^ 8) * derivative ℚ (derivative ℚ G) + (420 * X ^ 3 - 9216 * X ^ 4 + 72192 * X ^ 5 - 190464 * X ^ 6 + 98304 * X ^ 7) * derivative ℚ G + (5040 * X ^ 3 - 64896 * X ^ 4 + 196608 * X ^ 5 - 98304 * X ^ 6) * G =
      -1260 * X ^ 3 + 16224 * X ^ 4 - 49152 * X ^ 5 + 24576 * X ^ 6 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have hp0 : (4 * (X * X * X * X) : ℚ⟦X⟧) + (2 * (X * X) : ℚ⟦X⟧) * G + (1 * X + 4 * (X * X) : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((4 * (X * X * X * X) : ℚ⟦X⟧) + (2 * (X * X) : ℚ⟦X⟧) * G + (1 * X + 4 * (X * X) : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (16 * X ^ 3 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 + 8 * X : ℚ⟦X⟧) * G ^ 2 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hd1 : (16 * X ^ 3 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 + 8 * X : ℚ⟦X⟧) * G ^ 2 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (16 * (X * X * X) : ℚ⟦X⟧) + (2 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G + (2 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 + 8 * X : ℚ⟦X⟧) * G * G + (3 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((16 * (X * X * X) : ℚ⟦X⟧) + (2 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G + (2 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 + 8 * X : ℚ⟦X⟧) * G * G + (3 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (48 * X ^ 2 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (8 : ℚ⟦X⟧) * G ^ 2 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d3, d4, d8, d16]
    ring
  have hd2 : (48 * X ^ 2 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (8 : ℚ⟦X⟧) * G ^ 2 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (48 * (X * X) : ℚ⟦X⟧) + (2 * (X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X + 8 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (2 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G * G + (3 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((48 * (X * X) : ℚ⟦X⟧) + (2 * (X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X + 8 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (2 * X + 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 + 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G * G + (3 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G))) =
      (96 * X : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * (derivative ℚ G) + (6 * X + 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (6 + 48 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 + 48 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (48 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d8, d12, d32, d48]
    ring
  have hd3 : (96 * X : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * (derivative ℚ G) + (6 * X + 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (6 + 48 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 + 48 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (48 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((2 * X ^ 2 : ℚ⟦X⟧) + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G + (3 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((245 * X ^ 3 - 3920 * X ^ 4 + 23248 * X ^ 5 - 53888 * X ^ 6 - 19456 * X ^ 7 + 303104 * X ^ 8 - 393216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-420 * X ^ 3 - 3216 * X ^ 4 + 75648 * X ^ 5 - 390144 * X ^ 6 + 860160 * X ^ 7 - 786432 * X ^ 8) * derivative ℚ (derivative ℚ G) + (420 * X ^ 3 - 9216 * X ^ 4 + 72192 * X ^ 5 - 190464 * X ^ 6 + 98304 * X ^ 7) * derivative ℚ G + (5040 * X ^ 3 - 64896 * X ^ 4 + 196608 * X ^ 5 - 98304 * X ^ 6) * G - (-1260 * X ^ 3 + 16224 * X ^ 4 - 49152 * X ^ 5 + 24576 * X ^ 6)) = 0 := by
    linear_combination ((-94080 * X ^ 8 + 2241120 * X ^ 9 - 19611648 * X ^ 10 + 52273152 * X ^ 11 + 260014080 * X ^ 12 - 1909850112 * X ^ 13 + 1991245824 * X ^ 14 + 11802771456 * X ^ 15 - 26776436736 * X ^ 16 - 20937965568 * X ^ 17 + 77309411328 * X ^ 18 : ℚ⟦X⟧) + (-58800 * X ^ 7 + 3780000 * X ^ 8 - 68605440 * X ^ 9 + 526632960 * X ^ 10 - 1581711360 * X ^ 11 - 1124597760 * X ^ 12 + 16414408704 * X ^ 13 - 21038628864 * X ^ 14 - 40667971584 * X ^ 15 + 90194313216 * X ^ 16 : ℚ⟦X⟧) * G + (617400 * X ^ 6 - 12993120 * X ^ 7 + 92895360 * X ^ 8 - 179323392 * X ^ 9 - 688852992 * X ^ 10 + 2984509440 * X ^ 11 - 2721054720 * X ^ 12 + 2126512128 * X ^ 13 + 5033164800 * X ^ 14 - 84557168640 * X ^ 15 + 180388626432 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (470400 * X ^ 5 - 10002720 * X ^ 6 + 74803200 * X ^ 7 - 197133312 * X ^ 8 + 268124160 * X ^ 9 - 3438673920 * X ^ 10 + 13973323776 * X ^ 11 + 5184159744 * X ^ 12 - 107609063424 * X ^ 13 + 165893111808 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 + (117600 * X ^ 4 - 1096200 * X ^ 5 - 16625280 * X ^ 6 + 363843840 * X ^ 7 - 2183768064 * X ^ 8 + 3764428800 * X ^ 9 + 5351276544 * X ^ 10 - 25688014848 * X ^ 11 + 55087988736 * X ^ 12 - 109622329344 * X ^ 13 + 165893111808 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 + (70560 * X ^ 3 - 1464120 * X ^ 4 + 17915136 * X ^ 5 - 96161280 * X ^ 6 + 453132288 * X ^ 7 - 2881708032 * X ^ 8 + 4512940032 * X ^ 9 + 25060442112 * X ^ 10 - 90974453760 * X ^ 11 + 111132278784 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 + (577920 * X ^ 3 - 8963040 * X ^ 4 + 97003392 * X ^ 5 - 450210816 * X ^ 6 - 269795328 * X ^ 7 + 5148082176 * X ^ 8 - 12216827904 * X ^ 9 + 34304163840 * X ^ 10 - 61253615616 * X ^ 11 + 74088185856 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (1827840 * X ^ 3 - 9319680 * X ^ 4 + 33128448 * X ^ 5 - 372547584 * X ^ 6 - 1185742848 * X ^ 7 + 13545504768 * X ^ 8 - 27732738048 * X ^ 9 + 30601641984 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (5208000 * X ^ 3 - 14102016 * X ^ 4 - 262576128 * X ^ 5 + 807567360 * X ^ 6 - 1243545600 * X ^ 7 + 8476164096 * X ^ 8 - 13967032320 * X ^ 9 + 15300820992 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (12579840 * X ^ 3 - 99317760 * X ^ 4 - 125337600 * X ^ 5 + 1250820096 * X ^ 6 - 824180736 * X ^ 7 + 2013265920 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (19138560 * X ^ 3 - 220913664 * X ^ 4 + 493977600 * X ^ 5 + 244580352 * X ^ 6 - 339738624 * X ^ 7 + 805306368 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (15482880 * X ^ 3 - 199360512 * X ^ 4 + 603979776 * X ^ 5 - 301989888 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 + (5160960 * X ^ 3 - 66453504 * X ^ 4 + 201326592 * X ^ 5 - 100663296 * X ^ 6 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((70560 * X ^ 9 - 1290240 * X ^ 10 + 9488448 * X ^ 11 - 26947584 * X ^ 12 - 50061312 * X ^ 13 + 494370816 * X ^ 14 - 535560192 * X ^ 15 - 2950692864 * X ^ 16 + 6694109184 * X ^ 17 + 5234491392 * X ^ 18 - 19327352832 * X ^ 19 : ℚ⟦X⟧) + (58800 * X ^ 9 - 745920 * X ^ 10 + 1894656 * X ^ 11 + 14453760 * X ^ 12 - 91987968 * X ^ 13 + 91717632 * X ^ 14 + 486801408 * X ^ 15 - 1063256064 * X ^ 16 - 654311424 * X ^ 17 + 2415919104 * X ^ 18 : ℚ⟦X⟧) * (derivative ℚ G) + (94080 * X ^ 10 - 1317120 * X ^ 11 + 5916672 * X ^ 12 - 2838528 * X ^ 13 - 48857088 * X ^ 14 + 101449728 * X ^ 15 + 81788928 * X ^ 16 - 301989888 * X ^ 17 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (117600 * X ^ 8 - 1895040 * X ^ 9 + 19060992 * X ^ 10 - 125101056 * X ^ 11 + 355639296 * X ^ 12 + 422510592 * X ^ 13 - 4665114624 * X ^ 14 + 6329204736 * X ^ 15 + 11475615744 * X ^ 16 - 27380416512 * X ^ 17 : ℚ⟦X⟧) * G + (352800 * X ^ 8 - 5134080 * X ^ 9 + 26044416 * X ^ 10 - 37161984 * X ^ 11 - 90083328 * X ^ 12 + 158859264 * X ^ 13 + 512360448 * X ^ 14 + 103809024 * X ^ 15 - 3900702720 * X ^ 16 - 201326592 * X ^ 17 + 9663676416 * X ^ 18 : ℚ⟦X⟧) * G * (derivative ℚ G) + (58800 * X ^ 8 - 564480 * X ^ 9 + 687360 * X ^ 10 + 6217728 * X ^ 11 - 4399104 * X ^ 12 - 62619648 * X ^ 13 - 49545216 * X ^ 14 + 673185792 * X ^ 15 + 50331648 * X ^ 16 - 2415919104 * X ^ 17 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-88200 * X ^ 7 + 4593120 * X ^ 8 - 43519872 * X ^ 9 + 105881088 * X ^ 10 + 350447616 * X ^ 11 - 2072739840 * X ^ 12 + 2433220608 * X ^ 13 + 1953497088 * X ^ 14 - 4982833152 * X ^ 15 + 20132659200 * X ^ 16 - 54760833024 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 + (676200 * X ^ 7 - 7697760 * X ^ 8 + 16831104 * X ^ 9 + 128898048 * X ^ 10 - 710608896 * X ^ 11 + 521601024 * X ^ 12 + 3237740544 * X ^ 13 - 4863295488 * X ^ 14 - 5360320512 * X ^ 15 + 9663676416 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (205800 * X ^ 7 - 1975680 * X ^ 8 + 1841280 * X ^ 9 + 28535808 * X ^ 10 - 29822976 * X ^ 11 - 357433344 * X ^ 12 + 653721600 * X ^ 13 + 1174929408 * X ^ 14 - 1950351360 * X ^ 15 - 1107296256 * X ^ 16 - 4831838208 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-29400 * X ^ 6 + 4569600 * X ^ 7 - 46961280 * X ^ 8 + 137765376 * X ^ 9 - 27893760 * X ^ 10 + 701546496 * X ^ 11 - 6636699648 * X ^ 12 + 7826571264 * X ^ 13 + 34049359872 * X ^ 14 - 73685532672 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 + (970200 * X ^ 6 - 10741920 * X ^ 7 + 31843200 * X ^ 8 + 35252736 * X ^ 9 - 148752384 * X ^ 10 - 1067556864 * X ^ 11 + 3225550848 * X ^ 12 + 3189768192 * X ^ 13 - 10796138496 * X ^ 14 - 8355053568 * X ^ 15 + 12884901888 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (411600 * X ^ 6 - 3857280 * X ^ 7 + 1424640 * X ^ 8 + 81051648 * X ^ 9 - 205946880 * X ^ 10 - 174784512 * X ^ 11 + 250085376 * X ^ 12 + 2353004544 * X ^ 13 + 1509949440 * X ^ 14 - 14495514624 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (58800 * X ^ 5 + 2153760 * X ^ 6 - 15896160 * X ^ 7 - 99853056 * X ^ 8 + 1187331072 * X ^ 9 - 3448356864 * X ^ 10 + 935215104 * X ^ 11 + 11066671104 * X ^ 12 - 16955473920 * X ^ 13 + 30224154624 * X ^ 14 - 73685532672 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 + (764400 * X ^ 5 - 5179440 * X ^ 6 - 18207360 * X ^ 7 + 243216384 * X ^ 8 - 578675712 * X ^ 9 - 505159680 * X ^ 10 + 1744109568 * X ^ 11 + 6145179648 * X ^ 12 - 8707375104 * X ^ 13 - 12079595520 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (529200 * X ^ 5 - 5009760 * X ^ 6 + 5339520 * X ^ 7 + 51365376 * X ^ 8 + 89081856 * X ^ 9 - 1418526720 * X ^ 10 + 1965883392 * X ^ 11 + 4845993984 * X ^ 12 - 9097445376 * X ^ 13 + 301989888 * X ^ 14 - 14495514624 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (94080 * X ^ 4 + 742560 * X ^ 5 - 13488576 * X ^ 6 + 59179008 * X ^ 7 - 306819072 * X ^ 8 + 2160525312 * X ^ 9 - 6849429504 * X ^ 10 + 805306368 * X ^ 11 + 39283851264 * X ^ 12 - 64021856256 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (441000 * X ^ 4 - 1715280 * X ^ 5 - 17208192 * X ^ 6 + 80458752 * X ^ 7 + 319967232 * X ^ 8 - 2614431744 * X ^ 9 + 4063592448 * X ^ 10 + 3805544448 * X ^ 11 - 4309647360 * X ^ 12 - 10468982784 * X ^ 13 - 9663676416 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (396900 * X ^ 4 - 2681280 * X ^ 5 - 12859200 * X ^ 6 + 147967488 * X ^ 7 - 350889984 * X ^ 8 + 113393664 * X ^ 9 - 720764928 * X ^ 10 + 2802843648 * X ^ 11 + 9210691584 * X ^ 12 - 28991029248 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (88200 * X ^ 3 - 1123080 * X ^ 4 + 14859456 * X ^ 5 - 135868800 * X ^ 6 + 624350208 * X ^ 7 - 1265332224 * X ^ 8 + 419758080 * X ^ 9 + 2613313536 * X ^ 10 - 8663334912 * X ^ 11 + 25920798720 * X ^ 12 - 42681237504 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (132300 * X ^ 3 + 746760 * X ^ 4 - 17112192 * X ^ 5 + 68364288 * X ^ 6 - 87538176 * X ^ 7 + 450097152 * X ^ 8 - 4057694208 * X ^ 9 + 10483924992 * X ^ 10 + 1056964608 * X ^ 11 - 21139292160 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (198450 * X ^ 3 - 1270080 * X ^ 4 - 1302240 * X ^ 5 - 22432512 * X ^ 6 + 462907392 * X ^ 7 - 1803337728 * X ^ 8 + 1034944512 * X ^ 9 + 6618611712 * X ^ 10 - 10116661248 * X ^ 11 + 5234491392 * X ^ 12 - 19327352832 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (440160 * X ^ 3 - 6032256 * X ^ 4 + 49127040 * X ^ 5 - 308041728 * X ^ 6 + 1227300864 * X ^ 7 - 2006777856 * X ^ 8 - 2458386432 * X ^ 9 + 13967032320 * X ^ 10 - 17314086912 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (685440 * X ^ 3 - 2022528 * X ^ 4 - 42609408 * X ^ 5 + 359164416 * X ^ 6 - 1245456384 * X ^ 7 + 2083504128 * X ^ 8 - 2115895296 * X ^ 9 + 4407164928 * X ^ 10 - 301989888 * X ^ 11 - 12079595520 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (1270080 * X ^ 3 - 17216640 * X ^ 4 + 84390912 * X ^ 5 - 201517056 * X ^ 6 + 501792768 * X ^ 7 - 1655046144 * X ^ 8 + 726663168 * X ^ 9 + 11777605632 * X ^ 10 - 21743271936 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (1015140 * X ^ 3 - 13782336 * X ^ 4 + 83780352 * X ^ 5 - 320047104 * X ^ 6 + 929832960 * X ^ 7 - 1380581376 * X ^ 8 - 1538260992 * X ^ 9 + 7260340224 * X ^ 10 - 8657043456 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (1313760 * X ^ 3 - 2653248 * X ^ 4 - 96358656 * X ^ 5 + 744124416 * X ^ 6 - 2444328960 * X ^ 7 + 3544449024 * X ^ 8 + 103809024 * X ^ 9 - 3170893824 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (3069360 * X ^ 3 - 47416320 * X ^ 4 + 270929664 * X ^ 5 - 622798848 * X ^ 6 + 26542080 * X ^ 7 + 2172911616 * X ^ 8 - 3369074688 * X ^ 9 + 5662310400 * X ^ 10 - 10871635968 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (1202880 * X ^ 3 - 17395200 * X ^ 4 + 101584896 * X ^ 5 - 275152896 * X ^ 6 + 452198400 * X ^ 7 - 648019968 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (1330560 * X ^ 3 + 4097280 * X ^ 4 - 171150336 * X ^ 5 + 990609408 * X ^ 6 - 2524446720 * X ^ 7 + 2850029568 * X ^ 8 + 113246208 * X ^ 9 - 1409286144 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (3292800 * X ^ 3 - 52684800 * X ^ 4 + 312453120 * X ^ 5 - 724254720 * X ^ 6 - 261488640 * X ^ 7 + 4073717760 * X ^ 8 - 5284823040 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (766080 * X ^ 3 - 13347840 * X ^ 4 + 91029504 * X ^ 5 - 243007488 * X ^ 6 + 250085376 * X ^ 7 - 264241152 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (887040 * X ^ 3 + 6792192 * X ^ 4 - 159768576 * X ^ 5 + 823984128 * X ^ 6 - 1816657920 * X ^ 7 + 1660944384 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (1317120 * X ^ 3 - 21073920 * X ^ 4 + 124981248 * X ^ 5 - 289701888 * X ^ 6 - 104595456 * X ^ 7 + 1629487104 * X ^ 8 - 2113929216 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (322560 * X ^ 3 - 7077888 * X ^ 4 + 55443456 * X ^ 5 - 146276352 * X ^ 6 + 75497472 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 + (322560 * X ^ 3 + 2469888 * X ^ 4 - 58097664 * X ^ 5 + 299630592 * X ^ 6 - 660602880 * X ^ 7 + 603979776 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (107520 * X ^ 3 - 2359296 * X ^ 4 + 18481152 * X ^ 5 - 48758784 * X ^ 6 + 25165824 * X ^ 7 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-23520 * X ^ 10 + 369600 * X ^ 11 - 2283264 * X ^ 12 + 6383616 * X ^ 13 - 4374528 * X ^ 14 - 15335424 * X ^ 15 + 25165824 * X ^ 16 : ℚ⟦X⟧) + (-11760 * X ^ 10 + 141120 * X ^ 11 - 363264 * X ^ 12 - 1876992 * X ^ 13 + 11280384 * X ^ 14 - 10813440 * X ^ 15 - 39321600 * X ^ 16 + 75497472 * X ^ 17 : ℚ⟦X⟧) * (derivative ℚ G) + (-82320 * X ^ 9 + 913920 * X ^ 10 - 2103552 * X ^ 11 - 13584384 * X ^ 12 + 83705856 * X ^ 13 - 116785152 * X ^ 14 - 163577856 * X ^ 15 + 402653184 * X ^ 16 : ℚ⟦X⟧) * G + (-70560 * X ^ 9 + 846720 * X ^ 10 - 2744064 * X ^ 11 - 2230272 * X ^ 12 + 14118912 * X ^ 13 + 59277312 * X ^ 14 - 191102976 * X ^ 15 - 245366784 * X ^ 16 + 905969664 * X ^ 17 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-211680 * X ^ 8 + 2318400 * X ^ 9 - 7478784 * X ^ 10 + 359424 * X ^ 11 - 1916928 * X ^ 12 + 294912000 * X ^ 13 - 792723456 * X ^ 14 - 490733568 * X ^ 15 + 2415919104 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (-194040 * X ^ 8 + 1975680 * X ^ 9 - 2042496 * X ^ 10 - 39610368 * X ^ 11 + 139161600 * X ^ 12 + 7815168 * X ^ 13 - 454164480 * X ^ 14 - 103809024 * X ^ 15 - 75497472 * X ^ 16 + 3623878656 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-323400 * X ^ 7 + 2768640 * X ^ 8 - 504192 * X ^ 9 - 67169280 * X ^ 10 + 249704448 * X ^ 11 - 200048640 * X ^ 12 - 40108032 * X ^ 13 - 1352663040 * X ^ 14 + 6442450944 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 + (-382200 * X ^ 7 + 3951360 * X ^ 8 - 7290240 * X ^ 9 - 33954816 * X ^ 10 + 15814656 * X ^ 11 + 703070208 * X ^ 12 - 1238827008 * X ^ 13 - 2609381376 * X ^ 14 + 5574230016 * X ^ 15 + 1107296256 * X ^ 16 + 4831838208 * X ^ 17 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-382200 * X ^ 6 + 3192000 * X ^ 7 - 4366080 * X ^ 8 - 15742464 * X ^ 9 - 106487808 * X ^ 10 + 1065517056 * X ^ 11 - 2049245184 * X ^ 12 - 1388838912 * X ^ 13 + 3435134976 * X ^ 14 + 1308622848 * X ^ 15 + 6442450944 * X ^ 16 : ℚ⟦X⟧) * G ^ 4 + (-485100 * X ^ 6 + 4233600 * X ^ 7 + 3360960 * X ^ 8 - 126466560 * X ^ 9 + 325601280 * X ^ 10 + 160727040 * X ^ 11 - 542638080 * X ^ 12 - 2170552320 * X ^ 13 - 2642411520 * X ^ 14 + 18119393280 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-291060 * X ^ 5 + 1612800 * X ^ 6 + 7172928 * X ^ 7 - 80082432 * X ^ 8 + 245753856 * X ^ 9 - 372031488 * X ^ 10 + 1336541184 * X ^ 11 - 4331667456 * X ^ 12 - 905969664 * X ^ 13 + 12079595520 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 + (-476280 * X ^ 5 + 4304160 * X ^ 6 - 3140352 * X ^ 7 - 40582656 * X ^ 8 - 177887232 * X ^ 9 + 1596948480 * X ^ 10 - 1831403520 * X ^ 11 - 5770838016 * X ^ 12 + 10003415040 * X ^ 13 - 301989888 * X ^ 14 + 14495514624 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-158760 * X ^ 4 + 700560 * X ^ 5 + 1474944 * X ^ 6 + 8156928 * X ^ 7 - 213399552 * X ^ 8 + 1088299008 * X ^ 9 - 2038431744 * X ^ 10 + 462422016 * X ^ 11 - 251658240 * X ^ 12 + 100663296 * X ^ 13 + 8053063680 * X ^ 14 : ℚ⟦X⟧) * G ^ 6 + (-277830 * X ^ 4 + 1481760 * X ^ 5 + 14138208 * X ^ 6 - 125266176 * X ^ 7 + 270627840 * X ^ 8 - 87220224 * X ^ 9 + 805109760 * X ^ 10 - 2543321088 * X ^ 11 - 8455716864 * X ^ 12 + 25367150592 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-39690 * X ^ 3 - 302400 * X ^ 4 + 5155488 * X ^ 5 - 26558208 * X ^ 6 + 120259584 * X ^ 7 - 532979712 * X ^ 8 + 1882128384 * X ^ 9 - 3571974144 * X ^ 10 - 75497472 * X ^ 11 + 4831838208 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (-119070 * X ^ 3 + 635040 * X ^ 4 + 1684512 * X ^ 5 + 18567936 * X ^ 6 - 344291328 * X ^ 7 + 1283604480 * X ^ 8 - 661192704 * X ^ 9 - 4694999040 * X ^ 10 + 6908018688 * X ^ 11 - 3925868544 * X ^ 12 + 14495514624 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-192780 * X ^ 3 + 82224 * X ^ 4 + 13847040 * X ^ 5 - 100168704 * X ^ 6 + 425447424 * X ^ 7 - 1162248192 * X ^ 8 + 1993605120 * X ^ 9 - 2472542208 * X ^ 10 + 2415919104 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 + (-714420 * X ^ 3 + 9525600 * X ^ 4 - 45776448 * X ^ 5 + 111836160 * X ^ 6 - 327684096 * X ^ 7 + 1129807872 * X ^ 8 - 537919488 * X ^ 9 - 7417626624 * X ^ 10 + 13589544960 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-393120 * X ^ 3 - 367872 * X ^ 4 + 36844032 * X ^ 5 - 229847040 * X ^ 6 + 740130816 * X ^ 7 - 1458831360 * X ^ 8 + 1509949440 * X ^ 9 - 1006632960 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (-1587600 * X ^ 3 + 24460800 * X ^ 4 - 139357440 * X ^ 5 + 320133120 * X ^ 6 - 24084480 * X ^ 7 - 1061683200 * X ^ 8 + 1682964480 * X ^ 9 - 3145728000 * X ^ 10 + 6039797760 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-456960 * X ^ 3 - 2241024 * X ^ 4 + 65968128 * X ^ 5 - 355663872 * X ^ 6 + 871366656 * X ^ 7 - 1094713344 * X ^ 8 + 578813952 * X ^ 9 - 402653184 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 + (-1552320 * X ^ 3 + 24837120 * X ^ 4 - 147299328 * X ^ 5 + 341434368 * X ^ 6 + 123273216 * X ^ 7 - 1920466944 * X ^ 8 + 2491416576 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-322560 * X ^ 3 - 2469888 * X ^ 4 + 58097664 * X ^ 5 - 299630592 * X ^ 6 + 660602880 * X ^ 7 - 603979776 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 + (-564480 * X ^ 3 + 9031680 * X ^ 4 - 53563392 * X ^ 5 + 124157952 * X ^ 6 + 44826624 * X ^ 7 - 698351616 * X ^ 8 + 905969664 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-107520 * X ^ 3 - 823296 * X ^ 4 + 19365888 * X ^ 5 - 99876864 * X ^ 6 + 220200960 * X ^ 7 - 201326592 * X ^ 8 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((3920 * X ^ 11 - 62720 * X ^ 12 + 371968 * X ^ 13 - 862208 * X ^ 14 - 311296 * X ^ 15 + 4849664 * X ^ 16 - 6291456 * X ^ 17 : ℚ⟦X⟧) + (15680 * X ^ 10 - 188160 * X ^ 11 + 484352 * X ^ 12 + 2502656 * X ^ 13 - 15040512 * X ^ 14 + 14417920 * X ^ 15 + 52428800 * X ^ 16 - 100663296 * X ^ 17 : ℚ⟦X⟧) * G + (47040 * X ^ 9 - 564480 * X ^ 10 + 1829376 * X ^ 11 + 1486848 * X ^ 12 - 9412608 * X ^ 13 - 39518208 * X ^ 14 + 127401984 * X ^ 15 + 163577856 * X ^ 16 - 603979776 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 + (86240 * X ^ 8 - 878080 * X ^ 9 + 907776 * X ^ 10 + 17604608 * X ^ 11 - 61849600 * X ^ 12 - 3473408 * X ^ 13 + 201850880 * X ^ 14 + 46137344 * X ^ 15 + 33554432 * X ^ 16 - 1610612736 * X ^ 17 : ℚ⟦X⟧) * G ^ 3 + (127400 * X ^ 7 - 1317120 * X ^ 8 + 2430080 * X ^ 9 + 11318272 * X ^ 10 - 5271552 * X ^ 11 - 234356736 * X ^ 12 + 412942336 * X ^ 13 + 869793792 * X ^ 14 - 1858076672 * X ^ 15 - 369098752 * X ^ 16 - 1610612736 * X ^ 17 : ℚ⟦X⟧) * G ^ 4 + (129360 * X ^ 6 - 1128960 * X ^ 7 - 896256 * X ^ 8 + 33724416 * X ^ 9 - 86827008 * X ^ 10 - 42860544 * X ^ 11 + 144703488 * X ^ 12 + 578813952 * X ^ 13 + 704643072 * X ^ 14 - 4831838208 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 + (105840 * X ^ 5 - 956480 * X ^ 6 + 697856 * X ^ 7 + 9018368 * X ^ 8 + 39530496 * X ^ 9 - 354877440 * X ^ 10 + 406978560 * X ^ 11 + 1282408448 * X ^ 12 - 2222981120 * X ^ 13 + 67108864 * X ^ 14 - 3221225472 * X ^ 15 : ℚ⟦X⟧) * G ^ 6 + (52920 * X ^ 4 - 282240 * X ^ 5 - 2692992 * X ^ 6 + 23860224 * X ^ 7 - 51548160 * X ^ 8 + 16613376 * X ^ 9 - 153354240 * X ^ 10 + 484442112 * X ^ 11 + 1610612736 * X ^ 12 - 4831838208 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 + (19845 * X ^ 3 - 105840 * X ^ 4 - 280752 * X ^ 5 - 3094656 * X ^ 6 + 57381888 * X ^ 7 - 213934080 * X ^ 8 + 110198784 * X ^ 9 + 782499840 * X ^ 10 - 1151336448 * X ^ 11 + 654311424 * X ^ 12 - 2415919104 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 + (105840 * X ^ 3 - 1411200 * X ^ 4 + 6781696 * X ^ 5 - 16568320 * X ^ 6 + 48545792 * X ^ 7 - 167378944 * X ^ 8 + 79691776 * X ^ 9 + 1098907648 * X ^ 10 - 2013265920 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 + (211680 * X ^ 3 - 3261440 * X ^ 4 + 18580992 * X ^ 5 - 42684416 * X ^ 6 + 3211264 * X ^ 7 + 141557760 * X ^ 8 - 224395264 * X ^ 9 + 419430400 * X ^ 10 - 805306368 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 + (188160 * X ^ 3 - 3010560 * X ^ 4 + 17854464 * X ^ 5 - 41385984 * X ^ 6 - 14942208 * X ^ 7 + 232783872 * X ^ 8 - 301989888 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 + (62720 * X ^ 3 - 1003520 * X ^ 4 + 5951488 * X ^ 5 - 13795328 * X ^ 6 - 4980736 * X ^ 7 + 77594624 * X ^ 8 - 100663296 * X ^ 9 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (2 * X ^ 2 : ℚ⟦X⟧) + (2 * X + 8 * X ^ 2 : ℚ⟦X⟧) * G + (3 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3, k4] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 245 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-3920) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 23248 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-53888) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-19456) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C 303104 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * C (-393216) + derivative ℚ (derivative ℚ G) * X * X * X * C (-420) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-3216) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 75648 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-390144) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 860160 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-786432) + derivative ℚ G * X * X * X * C 420 +
      derivative ℚ G * X * X * X * X * C (-9216) + derivative ℚ G * X * X * X * X * X * C 72192 +
      derivative ℚ G * X * X * X * X * X * X * C (-190464) + derivative ℚ G * X * X * X * X * X * X * X * C 98304 +
      G * X * X * X * C 5040 + G * X * X * X * X * C (-64896) +
      G * X * X * X * X * X * C 196608 + G * X * X * X * X * X * X * C (-98304) =
      C (-1260) * X * X * X + C 16224 * X * X * X * X +
      C (-49152) * X * X * X * X * X + C 24576 * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) (m : ℕ) :
    245 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3920) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      23248 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-53888) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-19456) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 303104 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-393216) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-420) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-3216) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 75648 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-390144) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 860160 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-786432) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 420 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-9216) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 72192 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-190464) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 98304 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      5040 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-64896) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      196608 * coeff (m + 1 + 1 + 1 + 1) G + (-98304) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    51450 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-470400) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1394880 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1293312) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-116736) * coeff (0 + 1 + 1 + 1) G + (-12600) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-64320) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 907776 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2340864) * coeff (0 + 1 + 1 + 1) G + 1720320 * coeff (0 + 1 + 1) G +
      2100 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-36864) * coeff (0 + 1 + 1 + 1 + 1) G +
      216576 * coeff (0 + 1 + 1 + 1) G + (-380928) * coeff (0 + 1 + 1) G +
      98304 * coeff (0 + 1) G + 5040 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-64896) * coeff (0 + 1 + 1 + 1) G + 196608 * coeff (0 + 1 + 1) G +
      (-98304) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (X + 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    82320 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-823200) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2789760 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3233280) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-466944) * coeff (0 + 1 + 1 + 1 + 1) G + 1818624 * coeff (0 + 1 + 1 + 1) G +
      (-17640) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-96480) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1512960 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-4681728) * coeff (0 + 1 + 1 + 1 + 1) G +
      5160960 * coeff (0 + 1 + 1 + 1) G + (-1572864) * coeff (0 + 1 + 1) G +
      2520 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-46080) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      288768 * coeff (0 + 1 + 1 + 1 + 1) G + (-571392) * coeff (0 + 1 + 1 + 1) G +
      196608 * coeff (0 + 1 + 1) G + 5040 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-64896) * coeff (0 + 1 + 1 + 1 + 1) G + 196608 * coeff (0 + 1 + 1 + 1) G +
      (-98304) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A243764Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243764.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hn : ((-1) + (1) * W) * ((-4) + (-4) * W + (-4) * T + (-4) * T * W + (8) * PowerSeries.X + (8) * PowerSeries.X * W) = (64 * PowerSeries.X ^ 2 : PowerSeries ℚ) := by
    linear_combination ((-16)) * hT + ((-4) + (-4) * T + (8) * PowerSeries.X) * hW
  have hnu0 : (64 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (64 : PowerSeries ℚ) = 64 := A243764Aux.cnum 64
    simp [kc] at h'
  have hnu : (64 * PowerSeries.X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    have e : (64 * PowerSeries.X ^ 2 : PowerSeries ℚ) = PowerSeries.X ^ 2 * (64 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((-1) + (1) * W) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((-1) + (1) * W) ^ 4 * ((4 * PowerSeries.X ^ 4 : PowerSeries ℚ) + (2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (PowerSeries.X + 4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((-16) * PowerSeries.X ^ 3 + (24) * PowerSeries.X ^ 3 * T + (-8) * PowerSeries.X ^ 3 * T * W + (48) * PowerSeries.X ^ 4 + (-32) * PowerSeries.X ^ 4 * W + (16) * PowerSeries.X ^ 4 * T ^ 2 + (64) * PowerSeries.X ^ 5) * hT +
      ((-8) * PowerSeries.X ^ 3 + (4) * PowerSeries.X ^ 3 * W + (4) * PowerSeries.X ^ 3 * T + (-4) * PowerSeries.X ^ 3 * T * W + (4) * PowerSeries.X ^ 3 * T ^ 2 + (28) * PowerSeries.X ^ 4 + (-16) * PowerSeries.X ^ 4 * W + (4) * PowerSeries.X ^ 4 * W ^ 2 + (-16) * PowerSeries.X ^ 4 * T + (16) * PowerSeries.X ^ 4 * T ^ 2 + (32) * PowerSeries.X ^ 5) * hW +
      ((-1) * G ^ 2 + (3) * G ^ 2 * W + (-3) * G ^ 2 * W ^ 2 + (1) * G ^ 2 * W ^ 3 + (-1) * G ^ 3 + (3) * G ^ 3 * W + (-3) * G ^ 3 * W ^ 2 + (1) * G ^ 3 * W ^ 3 + (1) * PowerSeries.X * G + (-1) * PowerSeries.X * G * W + (-1) * PowerSeries.X * G * W ^ 2 + (1) * PowerSeries.X * G * W ^ 3 + (-2) * PowerSeries.X * G * T + (4) * PowerSeries.X * G * T * W + (-2) * PowerSeries.X * G * T * W ^ 2 + (2) * PowerSeries.X * G ^ 2 + (-4) * PowerSeries.X * G ^ 2 * W + (2) * PowerSeries.X * G ^ 2 * W ^ 2 + (-2) * PowerSeries.X * G ^ 2 * T + (4) * PowerSeries.X * G ^ 2 * T * W + (-2) * PowerSeries.X * G ^ 2 * T * W ^ 2 + (-4) * PowerSeries.X ^ 2 + (6) * PowerSeries.X ^ 2 * W + (-4) * PowerSeries.X ^ 2 * W ^ 2 + (2) * PowerSeries.X ^ 2 * W ^ 3 + (6) * PowerSeries.X ^ 2 * T + (-4) * PowerSeries.X ^ 2 * T * W + (-2) * PowerSeries.X ^ 2 * T * W ^ 2 + (-4) * PowerSeries.X ^ 2 * T ^ 2 + (4) * PowerSeries.X ^ 2 * T ^ 2 * W + (-8) * PowerSeries.X ^ 2 * G + (16) * PowerSeries.X ^ 2 * G * W + (-12) * PowerSeries.X ^ 2 * G * W ^ 2 + (4) * PowerSeries.X ^ 2 * G * W ^ 3 + (8) * PowerSeries.X ^ 2 * G * T + (-8) * PowerSeries.X ^ 2 * G * T * W + (-4) * PowerSeries.X ^ 2 * G * T ^ 2 + (4) * PowerSeries.X ^ 2 * G * T ^ 2 * W + (16) * PowerSeries.X ^ 3 + (-16) * PowerSeries.X ^ 3 * W + (8) * PowerSeries.X ^ 3 * W ^ 2 + (-32) * PowerSeries.X ^ 3 * T + (16) * PowerSeries.X ^ 3 * T * W + (-8) * PowerSeries.X ^ 3 * T * W ^ 2 + (24) * PowerSeries.X ^ 3 * T ^ 2 + (-8) * PowerSeries.X ^ 3 * T ^ 3) * hG
  have hP : (4 * PowerSeries.X ^ 4 : PowerSeries ℚ) + (2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (PowerSeries.X + 4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (-1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A243764Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A243764Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A243764Aux.rel G hP h0c m
      push_cast
      linear_combination r
