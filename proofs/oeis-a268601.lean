import OMAStatements.S_oeis_a268601

-- Problem: A268601: Expansion of 1/(2*f(x)) - 1/(4 - 2*g(x)), where f(x) = sqrt(1 - 4*x) and g(x) = sqrt(1 + 4*x).
-- Upstream: formal-conjectures statements/oeis-a268601.lean:0 (declaration OMA.S_oeis_a268601.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A268601Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 2 : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * G + (1 - 16 * X + 48 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (12 - 112 * X + 320 * X ^ 2 - 256 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 + (9 - 96 * X + 352 * X ^ 2 - 512 * X ^ 3 + 256 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (3 * X ^ 2 - 40 * X ^ 3 + 640 * X ^ 5 - 768 * X ^ 6) * derivative ℚ (derivative ℚ G) + (16 * X ^ 2 + 112 * X ^ 3 + 640 * X ^ 4 - 2304 * X ^ 5) * derivative ℚ G + (-68 * X ^ 2 - 160 * X ^ 3 - 576 * X ^ 4) * G =
      12 * X ^ 2 + 48 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d112 : derivative ℚ (112 : ℚ⟦X⟧) = 0 := dnum 112
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d320 : derivative ℚ (320 : ℚ⟦X⟧) = 0 := dnum 320
  have d336 : derivative ℚ (336 : ℚ⟦X⟧) = 0 := dnum 336
  have d352 : derivative ℚ (352 : ℚ⟦X⟧) = 0 := dnum 352
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d704 : derivative ℚ (704 : ℚ⟦X⟧) = 0 := dnum 704
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d960 : derivative ℚ (960 : ℚ⟦X⟧) = 0 := dnum 960
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1408 : derivative ℚ (1408 : ℚ⟦X⟧) = 0 := dnum 1408
  have d1536 : derivative ℚ (1536 : ℚ⟦X⟧) = 0 := dnum 1536
  have d2048 : derivative ℚ (2048 : ℚ⟦X⟧) = 0 := dnum 2048
  have hp0 : (4 * (X * X) : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * G + (1 - 16 * X + 48 * (X * X) : ℚ⟦X⟧) * G * G + (12 - 112 * X + 320 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * G * G * G + (9 - 96 * X + 352 * (X * X) - 512 * (X * X * X) + 256 * (X * X * X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((4 * (X * X) : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * G + (1 - 16 * X + 48 * (X * X) : ℚ⟦X⟧) * G * G + (12 - 112 * X + 320 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * G * G * G + (9 - 96 * X + 352 * (X * X) - 512 * (X * X * X) + 256 * (X * X * X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (8 * X : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 + 96 * X : ℚ⟦X⟧) * G ^ 2 + (36 - 336 * X + 960 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-112 + 640 * X - 768 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (36 - 384 * X + 1408 * X ^ 2 - 2048 * X ^ 3 + 1024 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-96 + 704 * X - 1536 * X ^ 2 + 1024 * X ^ 3 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4, d8, d9, d12, d16, d48, d96, d112, d256, d320, d352, d512]
    ring
  have hd1 : (8 * X : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 + 96 * X : ℚ⟦X⟧) * G ^ 2 + (36 - 336 * X + 960 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-112 + 640 * X - 768 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (36 - 384 * X + 1408 * X ^ 2 - 2048 * X ^ 3 + 1024 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-96 + 704 * X - 1536 * X ^ 2 + 1024 * X ^ 3 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (8 * X : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G + (2 - 32 * X + 96 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 + 96 * X : ℚ⟦X⟧) * G * G + (36 - 336 * X + 960 * (X * X) - 768 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-112 + 640 * X - 768 * (X * X) : ℚ⟦X⟧) * G * G * G + (36 - 384 * X + 1408 * (X * X) - 2048 * (X * X * X) + 1024 * (X * X * X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-96 + 704 * X - 1536 * (X * X) + 1024 * (X * X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((8 * X : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 : ℚ⟦X⟧) * G + (2 - 32 * X + 96 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 + 96 * X : ℚ⟦X⟧) * G * G + (36 - 336 * X + 960 * (X * X) - 768 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-112 + 640 * X - 768 * (X * X) : ℚ⟦X⟧) * G * G * G + (36 - 384 * X + 1408 * (X * X) - 2048 * (X * X * X) + 1024 * (X * X * X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-96 + 704 * X - 1536 * (X * X) + 1024 * (X * X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (8 : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-64 + 384 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (72 - 672 * X + 1920 * X ^ 2 - 1536 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (96 : ℚ⟦X⟧) * G ^ 2 + (36 - 336 * X + 960 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-672 + 3840 * X - 4608 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (108 - 1152 * X + 4224 * X ^ 2 - 6144 * X ^ 3 + 3072 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (640 - 1536 * X : ℚ⟦X⟧) * G ^ 3 + (36 - 384 * X + 1408 * X ^ 2 - 2048 * X ^ 3 + 1024 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-768 + 5632 * X - 12288 * X ^ 2 + 8192 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (704 - 3072 * X + 3072 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d8, d16, d32, d36, d96, d112, d336, d384, d640, d704, d768, d960, d1024, d1408, d1536, d2048]
    ring
  have hd2 : (8 : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-64 + 384 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (72 - 672 * X + 1920 * X ^ 2 - 1536 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (96 : ℚ⟦X⟧) * G ^ 2 + (36 - 336 * X + 960 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-672 + 3840 * X - 4608 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (108 - 1152 * X + 4224 * X ^ 2 - 6144 * X ^ 3 + 3072 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (640 - 1536 * X : ℚ⟦X⟧) * G ^ 3 + (36 - 384 * X + 1408 * X ^ 2 - 2048 * X ^ 3 + 1024 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-768 + 5632 * X - 12288 * X ^ 2 + 8192 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (704 - 3072 * X + 3072 * X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-2 + 8 * X : ℚ⟦X⟧) + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * G + (36 - 336 * X + 960 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (36 - 384 * X + 1408 * X ^ 2 - 2048 * X ^ 3 + 1024 * X ^ 4 : ℚ⟦X⟧) * G ^ 3) ^ 3 * ((3 * X ^ 2 - 40 * X ^ 3 + 640 * X ^ 5 - 768 * X ^ 6) * derivative ℚ (derivative ℚ G) + (16 * X ^ 2 + 112 * X ^ 3 + 640 * X ^ 4 - 2304 * X ^ 5) * derivative ℚ G + (-68 * X ^ 2 - 160 * X ^ 3 - 576 * X ^ 4) * G - (12 * X ^ 2 + 48 * X ^ 3)) = 0 := by
    linear_combination ((416 * X ^ 2 - 4352 * X ^ 3 + 19968 * X ^ 4 - 106496 * X ^ 5 + 548864 * X ^ 6 - 1376256 * X ^ 7 + 1179648 * X ^ 8 : ℚ⟦X⟧) + (-1152 * X ^ 2 + 26112 * X ^ 3 - 153600 * X ^ 4 - 319488 * X ^ 5 + 6586368 * X ^ 6 - 25559040 * X ^ 7 + 39321600 * X ^ 8 - 18874368 * X ^ 9 : ℚ⟦X⟧) * G + (-12480 * X ^ 2 + 164352 * X ^ 3 - 651264 * X ^ 4 - 958464 * X ^ 5 + 17989632 * X ^ 6 - 70385664 * X ^ 7 + 128974848 * X ^ 8 - 106954752 * X ^ 9 + 37748736 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (2560 * X ^ 2 - 219136 * X ^ 3 + 3022848 * X ^ 4 - 18841600 * X ^ 5 + 69074944 * X ^ 6 - 168296448 * X ^ 7 + 257949696 * X ^ 8 - 176160768 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (132480 * X ^ 2 - 2706432 * X ^ 3 + 22966272 * X ^ 4 - 107593728 * X ^ 5 + 323616768 * X ^ 6 - 719585280 * X ^ 7 + 1242562560 * X ^ 8 - 1396703232 * X ^ 9 + 679477248 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (235008 * X ^ 2 - 4884480 * X ^ 3 + 42958848 * X ^ 4 - 211943424 * X ^ 5 + 672399360 * X ^ 6 - 1550843904 * X ^ 7 + 2843738112 * X ^ 8 - 3925868544 * X ^ 9 + 3321888768 * X ^ 10 - 1207959552 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 + (117504 * X ^ 2 - 2598912 * X ^ 3 + 24735744 * X ^ 4 - 134610944 * X ^ 5 + 477495296 * X ^ 6 - 1223688192 * X ^ 7 + 2455764992 * X ^ 8 - 3858759680 * X ^ 9 + 4278190080 * X ^ 10 - 2818572288 * X ^ 11 + 805306368 * X ^ 12 : ℚ⟦X⟧) * G ^ 6) * hP +
      ((160 * X ^ 2 - 1680 * X ^ 3 + 3712 * X ^ 4 + 10496 * X ^ 5 - 12288 * X ^ 6 - 225280 * X ^ 7 + 688128 * X ^ 8 - 589824 * X ^ 9 : ℚ⟦X⟧) + (12 * X ^ 2 - 400 * X ^ 3 + 4544 * X ^ 4 - 17664 * X ^ 5 - 23552 * X ^ 6 + 348160 * X ^ 7 - 835584 * X ^ 8 + 589824 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (-560 * X ^ 2 + 13760 * X ^ 3 - 113664 * X ^ 4 + 367616 * X ^ 5 + 40960 * X ^ 6 - 3981312 * X ^ 7 + 13369344 * X ^ 8 - 19660800 * X ^ 9 + 9437184 * X ^ 10 : ℚ⟦X⟧) * G + (420 * X ^ 2 - 10976 * X ^ 3 + 95104 * X ^ 4 - 259584 * X ^ 5 - 753664 * X ^ 6 + 6250496 * X ^ 7 - 13860864 * X ^ 8 + 11403264 * X ^ 9 - 2359296 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-5984 * X ^ 2 + 98336 * X ^ 3 - 592128 * X ^ 4 + 1534976 * X ^ 5 - 1150976 * X ^ 6 - 4128768 * X ^ 7 + 23396352 * X ^ 8 - 57409536 * X ^ 9 + 53477376 * X ^ 10 - 18874368 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (6912 * X ^ 3 - 184320 * X ^ 4 + 1671168 * X ^ 5 - 5308416 * X ^ 6 - 9043968 * X ^ 7 + 110100480 * X ^ 8 - 301989888 * X ^ 9 + 352321536 * X ^ 10 - 150994944 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (3072 * X ^ 2 - 148480 * X ^ 3 + 1863680 * X ^ 4 - 9256960 * X ^ 5 + 13303808 * X ^ 6 + 41156608 * X ^ 7 - 162529280 * X ^ 8 + 171966464 * X ^ 9 - 50331648 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-8640 * X ^ 2 + 283392 * X ^ 3 - 3557376 * X ^ 4 + 20922368 * X ^ 5 - 42762240 * X ^ 6 - 164495360 * X ^ 7 + 1293942784 * X ^ 8 - 3636461568 * X ^ 9 + 5305794560 * X ^ 10 - 3976200192 * X ^ 11 + 1207959552 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (77184 * X ^ 2 - 1860096 * X ^ 3 + 17745920 * X ^ 4 - 81780736 * X ^ 5 + 153714688 * X ^ 6 + 155582464 * X ^ 7 - 1290272768 * X ^ 8 + 2405433344 * X ^ 9 - 1962934272 * X ^ 10 + 603979776 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 + (-19440 * X ^ 2 + 648000 * X ^ 3 - 8398080 * X ^ 4 + 52853760 * X ^ 5 - 136273920 * X ^ 6 - 260014080 * X ^ 7 + 3124101120 * X ^ 8 - 10687610880 * X ^ 9 + 19802357760 * X ^ 10 - 21202206720 * X ^ 11 + 12331253760 * X ^ 12 - 3019898880 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (139968 * X ^ 2 - 3483648 * X ^ 3 + 35251200 * X ^ 4 - 180486144 * X ^ 5 + 433815552 * X ^ 6 + 22020096 * X ^ 7 - 2990014464 * X ^ 8 + 8153726976 * X ^ 9 - 10506731520 * X ^ 10 + 6845104128 * X ^ 11 - 1811939328 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 + (-11664 * X ^ 2 + 404352 * X ^ 3 - 5557248 * X ^ 4 + 38430720 * X ^ 5 - 124047360 * X ^ 6 - 46989312 * X ^ 7 + 2082471936 * X ^ 8 - 8911847424 * X ^ 9 + 20431503360 * X ^ 10 - 28563210240 * X ^ 11 + 24360517632 * X ^ 12 - 11676942336 * X ^ 13 + 2415919104 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (72576 * X ^ 2 - 1921536 * X ^ 3 + 21067776 * X ^ 4 - 120791040 * X ^ 5 + 355401728 * X ^ 6 - 243531776 * X ^ 7 - 1926234112 * X ^ 8 + 7495221248 * X ^ 9 - 13329498112 * X ^ 10 + 13254000640 * X ^ 11 - 7113539584 * X ^ 12 + 1610612736 * X ^ 13 : ℚ⟦X⟧) * G ^ 6) * hd1 +
      ((12 * X ^ 2 - 256 * X ^ 3 + 1472 * X ^ 4 - 23552 * X ^ 6 + 65536 * X ^ 7 - 49152 * X ^ 8 : ℚ⟦X⟧) + (-24 * X ^ 2 + 800 * X ^ 3 - 9088 * X ^ 4 + 35328 * X ^ 5 + 47104 * X ^ 6 - 696320 * X ^ 7 + 1671168 * X ^ 8 - 1179648 * X ^ 9 : ℚ⟦X⟧) * G + (-420 * X ^ 2 + 10976 * X ^ 3 - 95104 * X ^ 4 + 259584 * X ^ 5 + 753664 * X ^ 6 - 6250496 * X ^ 7 + 13860864 * X ^ 8 - 11403264 * X ^ 9 + 2359296 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (-4608 * X ^ 3 + 122880 * X ^ 4 - 1114112 * X ^ 5 + 3538944 * X ^ 6 + 6029312 * X ^ 7 - 73400320 * X ^ 8 + 201326592 * X ^ 9 - 234881024 * X ^ 10 + 100663296 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (4320 * X ^ 2 - 141696 * X ^ 3 + 1778688 * X ^ 4 - 10461184 * X ^ 5 + 21381120 * X ^ 6 + 82247680 * X ^ 7 - 646971392 * X ^ 8 + 1818230784 * X ^ 9 - 2652897280 * X ^ 10 + 1988100096 * X ^ 11 - 603979776 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 + (7776 * X ^ 2 - 259200 * X ^ 3 + 3359232 * X ^ 4 - 21141504 * X ^ 5 + 54509568 * X ^ 6 + 104005632 * X ^ 7 - 1249640448 * X ^ 8 + 4275044352 * X ^ 9 - 7920943104 * X ^ 10 + 8480882688 * X ^ 11 - 4932501504 * X ^ 12 + 1207959552 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (3888 * X ^ 2 - 134784 * X ^ 3 + 1852416 * X ^ 4 - 12810240 * X ^ 5 + 41349120 * X ^ 6 + 15663104 * X ^ 7 - 694157312 * X ^ 8 + 2970615808 * X ^ 9 - 6810501120 * X ^ 10 + 9521070080 * X ^ 11 - 8120172544 * X ^ 12 + 3892314112 * X ^ 13 - 805306368 * X ^ 14 : ℚ⟦X⟧) * G ^ 6) * hd2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have k36 : constantCoeff (36 : ℚ⟦X⟧) = 36 := cnum 36
  have hPG : (-2 + 8 * X : ℚ⟦X⟧) + (2 - 32 * X + 96 * X ^ 2 : ℚ⟦X⟧) * G + (36 - 336 * X + 960 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (36 - 384 * X + 1408 * X ^ 2 - 2048 * X ^ 3 + 1024 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2, k36] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 2 : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * G + (1 - 16 * X + 48 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (12 - 112 * X + 320 * X ^ 2 - 256 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 + (9 - 96 * X + 352 * X ^ 2 - 512 * X ^ 3 + 256 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 3 + derivative ℚ (derivative ℚ G) * X * X * X * C (-40) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 640 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-768) +
      derivative ℚ G * X * X * C 16 + derivative ℚ G * X * X * X * C 112 +
      derivative ℚ G * X * X * X * X * C 640 + derivative ℚ G * X * X * X * X * X * C (-2304) +
      G * X * X * C (-68) + G * X * X * X * C (-160) +
      G * X * X * X * X * C (-576) =
      C 12 * X * X + C 48 * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 2 : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * G + (1 - 16 * X + 48 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (12 - 112 * X + 320 * X ^ 2 - 256 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 + (9 - 96 * X + 352 * X ^ 2 - 512 * X ^ 3 + 256 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    3 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-40) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      640 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-768) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      16 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 112 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      640 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-2304) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-68) * coeff (m + 1 + 1 + 1 + 1) G + (-160) * coeff (m + 1 + 1 + 1) G +
      (-576) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 2 : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * G + (1 - 16 * X + 48 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (12 - 112 * X + 320 * X ^ 2 - 256 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 + (9 - 96 * X + 352 * X ^ 2 - 512 * X ^ 3 + 256 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    36 * coeff (0 + 1 + 1 + 1 + 1) G + (-240) * coeff (0 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1 + 1) G + 224 * coeff (0 + 1 + 1) G +
      640 * coeff (0 + 1) G + (-68) * coeff (0 + 1 + 1) G +
      (-160) * coeff (0 + 1) G + (-576) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 2 : ℚ⟦X⟧) + (-2 + 8 * X : ℚ⟦X⟧) * G + (1 - 16 * X + 48 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (12 - 112 * X + 320 * X ^ 2 - 256 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 + (9 - 96 * X + 352 * X ^ 2 - 512 * X ^ 3 + 256 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-480) * coeff (0 + 1 + 1 + 1 + 1) G +
      1280 * coeff (0 + 1 + 1) G + 64 * coeff (0 + 1 + 1 + 1 + 1) G +
      336 * coeff (0 + 1 + 1 + 1) G + 1280 * coeff (0 + 1 + 1) G +
      (-2304) * coeff (0 + 1) G + (-68) * coeff (0 + 1 + 1 + 1) G +
      (-160) * coeff (0 + 1 + 1) G + (-576) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A268601Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a268601.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hn : ((8) * T + (-4) * T * W) * ((384) * T ^ 3 + (192) * T ^ 3 * W + (-512) * PowerSeries.X * T ^ 3 + (-256) * PowerSeries.X * T ^ 3 * W) = (2304 - 24576 * PowerSeries.X + 90112 * PowerSeries.X ^ 2 - 131072 * PowerSeries.X ^ 3 + 65536 * PowerSeries.X ^ 4 : PowerSeries ℚ) := by
    linear_combination ((2304) + (2304) * T ^ 2 + (-15360) * PowerSeries.X + (-6144) * PowerSeries.X * T ^ 2 + (28672) * PowerSeries.X ^ 2 + (4096) * PowerSeries.X ^ 2 * T ^ 2 + (-16384) * PowerSeries.X ^ 3) * hT + ((-768) * T ^ 4 + (1024) * PowerSeries.X * T ^ 4) * hW
  have hnu0 : (2304 - 24576 * PowerSeries.X + 90112 * PowerSeries.X ^ 2 - 131072 * PowerSeries.X ^ 3 + 65536 * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (2304 : PowerSeries ℚ) = 2304 := A268601Aux.cnum 2304
    simp [kc] at h'
  have hnu : (2304 - 24576 * PowerSeries.X + 90112 * PowerSeries.X ^ 2 - 131072 * PowerSeries.X ^ 3 + 65536 * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    have e : (2304 - 24576 * PowerSeries.X + 90112 * PowerSeries.X ^ 2 - 131072 * PowerSeries.X ^ 3 + 65536 * PowerSeries.X ^ 4 : PowerSeries ℚ) = PowerSeries.X ^ 0 * (2304 - 24576 * PowerSeries.X + 90112 * PowerSeries.X ^ 2 - 131072 * PowerSeries.X ^ 3 + 65536 * PowerSeries.X ^ 4 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 0 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((8) * T + (-4) * T * W) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((8) * T + (-4) * T * W) ^ 4 * ((4 * PowerSeries.X ^ 2 : PowerSeries ℚ) + (-2 + 8 * PowerSeries.X : PowerSeries ℚ) * G + (1 - 16 * PowerSeries.X + 48 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (12 - 112 * PowerSeries.X + 320 * PowerSeries.X ^ 2 - 256 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3 + (9 - 96 * PowerSeries.X + 352 * PowerSeries.X ^ 2 - 512 * PowerSeries.X ^ 3 + 256 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((-5904) + (5760) * W + (-7680) * T + (7872) * T * W + (3280) * T ^ 2 + (-3200) * T ^ 2 * W + (24384) * PowerSeries.X + (-33792) * PowerSeries.X * W + (4096) * PowerSeries.X * T + (-22016) * PowerSeries.X * T * W + (-7424) * PowerSeries.X * T ^ 2 + (12800) * PowerSeries.X * T ^ 2 * W + (24064) * PowerSeries.X ^ 2 + (40960) * PowerSeries.X ^ 2 * W + (131072) * PowerSeries.X ^ 2 * T + (-61440) * PowerSeries.X ^ 2 * T * W + (13824) * PowerSeries.X ^ 2 * T ^ 2 + (-38912) * PowerSeries.X ^ 2 * T ^ 2 * W + (-129024) * PowerSeries.X ^ 3 + (16384) * PowerSeries.X ^ 3 * W + (-65536) * PowerSeries.X ^ 3 * T + (90112) * PowerSeries.X ^ 3 * T * W + (126976) * PowerSeries.X ^ 3 * T ^ 2 + (-40960) * PowerSeries.X ^ 3 * T ^ 2 * W + (77824) * PowerSeries.X ^ 4 + (-32768) * PowerSeries.X ^ 4 * W + (-131072) * PowerSeries.X ^ 4 * T + (16384) * PowerSeries.X ^ 4 * T * W + (20480) * PowerSeries.X ^ 4 * T ^ 2 + (16384) * PowerSeries.X ^ 5) * hT +
      ((3600) + (-1152) * W + (144) * W ^ 2 + (6144) * T + (-2496) * T * W + (384) * T * W ^ 2 + (-4448) * T ^ 2 + (640) * T ^ 2 * W + (64) * T ^ 2 * W ^ 2 + (-6016) * T ^ 3 + (2176) * T ^ 3 * W + (-256) * T ^ 3 * W ^ 2 + (1600) * T ^ 4 + (-256) * T ^ 4 * W + (-37824) * PowerSeries.X + (12288) * PowerSeries.X * W + (-1536) * PowerSeries.X * W ^ 2 + (-51200) * PowerSeries.X * T + (22528) * PowerSeries.X * T * W + (-3584) * PowerSeries.X * T * W ^ 2 + (29952) * PowerSeries.X * T ^ 2 + (-2560) * PowerSeries.X * T ^ 2 * W + (-1024) * PowerSeries.X * T ^ 2 * W ^ 2 + (26112) * PowerSeries.X * T ^ 3 + (-10240) * PowerSeries.X * T ^ 3 * W + (1024) * PowerSeries.X * T ^ 3 * W ^ 2 + (-7168) * PowerSeries.X * T ^ 4 + (1024) * PowerSeries.X * T ^ 4 * W + (134656) * PowerSeries.X ^ 2 + (-45056) * PowerSeries.X ^ 2 * W + (5632) * PowerSeries.X ^ 2 * W ^ 2 + (106496) * PowerSeries.X ^ 2 * T + (-59392) * PowerSeries.X ^ 2 * T * W + (10240) * PowerSeries.X ^ 2 * T * W ^ 2 + (-77824) * PowerSeries.X ^ 2 * T ^ 2 + (6144) * PowerSeries.X ^ 2 * T ^ 2 * W + (3072) * PowerSeries.X ^ 2 * T ^ 2 * W ^ 2 + (-2048) * PowerSeries.X ^ 2 * T ^ 3 + (6144) * PowerSeries.X ^ 2 * T ^ 3 * W + (28672) * PowerSeries.X ^ 2 * T ^ 4 + (-8192) * PowerSeries.X ^ 2 * T ^ 4 * W + (1024) * PowerSeries.X ^ 2 * T ^ 4 * W ^ 2 + (-182272) * PowerSeries.X ^ 3 + (65536) * PowerSeries.X ^ 3 * W + (-8192) * PowerSeries.X ^ 3 * W ^ 2 + (32768) * PowerSeries.X ^ 3 * T + (32768) * PowerSeries.X ^ 3 * T * W + (-8192) * PowerSeries.X ^ 3 * T * W ^ 2 + (110592) * PowerSeries.X ^ 3 * T ^ 2 + (-24576) * PowerSeries.X ^ 3 * T ^ 2 * W + (-24576) * PowerSeries.X ^ 3 * T ^ 3 + (4096) * PowerSeries.X ^ 3 * T ^ 4 + (69632) * PowerSeries.X ^ 4 + (-32768) * PowerSeries.X ^ 4 * W + (4096) * PowerSeries.X ^ 4 * W ^ 2 + (-131072) * PowerSeries.X ^ 4 * T + (16384) * PowerSeries.X ^ 4 * T * W + (24576) * PowerSeries.X ^ 4 * T ^ 2 + (16384) * PowerSeries.X ^ 5) * hW +
      ((576) + (-864) * W + (432) * W ^ 2 + (-72) * W ^ 3 + (672) * T + (-1440) * T * W + (936) * T * W ^ 2 + (-192) * T * W ^ 3 + (-848) * T ^ 2 + (936) * T ^ 2 * W + (-192) * T ^ 2 * W ^ 2 + (-32) * T ^ 2 * W ^ 3 + (-840) * T ^ 3 + (1472) * T ^ 3 * W + (-800) * T ^ 3 * W ^ 2 + (128) * T ^ 3 * W ^ 3 + (1152) * G * T + (-1728) * G * T * W + (864) * G * T * W ^ 2 + (-144) * G * T * W ^ 3 + (1920) * G * T ^ 2 + (-3456) * G * T ^ 2 * W + (2016) * G * T ^ 2 * W ^ 2 + (-384) * G * T ^ 2 * W ^ 3 + (-736) * G * T ^ 3 + (624) * G * T ^ 3 * W + (-64) * G * T ^ 3 * W ^ 3 + (2304) * G ^ 2 * T ^ 2 + (-3456) * G ^ 2 * T ^ 2 * W + (1728) * G ^ 2 * T ^ 2 * W ^ 2 + (-288) * G ^ 2 * T ^ 2 * W ^ 3 + (4992) * G ^ 2 * T ^ 3 + (-8064) * G ^ 2 * T ^ 3 * W + (4320) * G ^ 2 * T ^ 3 * W ^ 2 + (-768) * G ^ 2 * T ^ 3 * W ^ 3 + (4608) * G ^ 3 * T ^ 3 + (-6912) * G ^ 3 * T ^ 3 * W + (3456) * G ^ 3 * T ^ 3 * W ^ 2 + (-576) * G ^ 3 * T ^ 3 * W ^ 3 + (-6144) * PowerSeries.X + (9216) * PowerSeries.X * W + (-4608) * PowerSeries.X * W ^ 2 + (768) * PowerSeries.X * W ^ 3 + (-5120) * PowerSeries.X * T + (12288) * PowerSeries.X * T * W + (-8448) * PowerSeries.X * T * W ^ 2 + (1792) * PowerSeries.X * T * W ^ 3 + (5632) * PowerSeries.X * T ^ 2 + (-5888) * PowerSeries.X * T ^ 2 * W + (512) * PowerSeries.X * T ^ 2 * W ^ 2 + (512) * PowerSeries.X * T ^ 2 * W ^ 3 + (3328) * PowerSeries.X * T ^ 3 + (-6400) * PowerSeries.X * T ^ 3 * W + (3584) * PowerSeries.X * T ^ 3 * W ^ 2 + (-512) * PowerSeries.X * T ^ 3 * W ^ 3 + (-12288) * PowerSeries.X * G * T + (18432) * PowerSeries.X * G * T * W + (-9216) * PowerSeries.X * G * T * W ^ 2 + (1536) * PowerSeries.X * G * T * W ^ 3 + (-16384) * PowerSeries.X * G * T ^ 2 + (30720) * PowerSeries.X * G * T ^ 2 * W + (-18432) * PowerSeries.X * G * T ^ 2 * W ^ 2 + (3584) * PowerSeries.X * G * T ^ 2 * W ^ 3 + (3072) * PowerSeries.X * G * T ^ 3 + (-512) * PowerSeries.X * G * T ^ 3 * W + (-2560) * PowerSeries.X * G * T ^ 3 * W ^ 2 + (1024) * PowerSeries.X * G * T ^ 3 * W ^ 3 + (-24576) * PowerSeries.X * G ^ 2 * T ^ 2 + (36864) * PowerSeries.X * G ^ 2 * T ^ 2 * W + (-18432) * PowerSeries.X * G ^ 2 * T ^ 2 * W ^ 2 + (3072) * PowerSeries.X * G ^ 2 * T ^ 2 * W ^ 3 + (-45056) * PowerSeries.X * G ^ 2 * T ^ 3 + (73728) * PowerSeries.X * G ^ 2 * T ^ 3 * W + (-39936) * PowerSeries.X * G ^ 2 * T ^ 3 * W ^ 2 + (7168) * PowerSeries.X * G ^ 2 * T ^ 3 * W ^ 3 + (-49152) * PowerSeries.X * G ^ 3 * T ^ 3 + (73728) * PowerSeries.X * G ^ 3 * T ^ 3 * W + (-36864) * PowerSeries.X * G ^ 3 * T ^ 3 * W ^ 2 + (6144) * PowerSeries.X * G ^ 3 * T ^ 3 * W ^ 3 + (22528) * PowerSeries.X ^ 2 + (-33792) * PowerSeries.X ^ 2 * W + (16896) * PowerSeries.X ^ 2 * W ^ 2 + (-2816) * PowerSeries.X ^ 2 * W ^ 3 + (7168) * PowerSeries.X ^ 2 * T + (-27648) * PowerSeries.X ^ 2 * T * W + (22272) * PowerSeries.X ^ 2 * T * W ^ 2 + (-5120) * PowerSeries.X ^ 2 * T * W ^ 3 + (-11776) * PowerSeries.X ^ 2 * T ^ 2 + (14080) * PowerSeries.X ^ 2 * T ^ 2 * W + (-1024) * PowerSeries.X ^ 2 * T ^ 2 * W ^ 2 + (-1536) * PowerSeries.X ^ 2 * T ^ 2 * W ^ 3 + (1280) * PowerSeries.X ^ 2 * T ^ 3 + (1024) * PowerSeries.X ^ 2 * T ^ 3 * W + (-1536) * PowerSeries.X ^ 2 * T ^ 3 * W ^ 2 + (45056) * PowerSeries.X ^ 2 * G * T + (-67584) * PowerSeries.X ^ 2 * G * T * W + (33792) * PowerSeries.X ^ 2 * G * T * W ^ 2 + (-5632) * PowerSeries.X ^ 2 * G * T * W ^ 3 + (36864) * PowerSeries.X ^ 2 * G * T ^ 2 + (-77824) * PowerSeries.X ^ 2 * G * T ^ 2 * W + (50176) * PowerSeries.X ^ 2 * G * T ^ 2 * W ^ 2 + (-10240) * PowerSeries.X ^ 2 * G * T ^ 2 * W ^ 3 + (-5120) * PowerSeries.X ^ 2 * G * T ^ 3 + (-1536) * PowerSeries.X ^ 2 * G * T ^ 3 * W + (8192) * PowerSeries.X ^ 2 * G * T ^ 3 * W ^ 2 + (-3072) * PowerSeries.X ^ 2 * G * T ^ 3 * W ^ 3 + (90112) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 + (-135168) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 * W + (67584) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 * W ^ 2 + (-11264) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 * W ^ 3 + (118784) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 + (-200704) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 * W + (111616) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 * W ^ 2 + (-20480) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 * W ^ 3 + (180224) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 3 + (-270336) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 3 * W + (135168) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 3 * W ^ 2 + (-22528) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 3 * W ^ 3 + (-32768) * PowerSeries.X ^ 3 + (49152) * PowerSeries.X ^ 3 * W + (-24576) * PowerSeries.X ^ 3 * W ^ 2 + (4096) * PowerSeries.X ^ 3 * W ^ 3 + (16384) * PowerSeries.X ^ 3 * T + (-12288) * PowerSeries.X ^ 3 * T * W ^ 2 + (4096) * PowerSeries.X ^ 3 * T * W ^ 3 + (8192) * PowerSeries.X ^ 3 * T ^ 2 + (-20480) * PowerSeries.X ^ 3 * T ^ 2 * W + (8192) * PowerSeries.X ^ 3 * T ^ 2 * W ^ 2 + (-4096) * PowerSeries.X ^ 3 * T ^ 3 + (4096) * PowerSeries.X ^ 3 * T ^ 3 * W + (-65536) * PowerSeries.X ^ 3 * G * T + (98304) * PowerSeries.X ^ 3 * G * T * W + (-49152) * PowerSeries.X ^ 3 * G * T * W ^ 2 + (8192) * PowerSeries.X ^ 3 * G * T * W ^ 3 + (32768) * PowerSeries.X ^ 3 * G * T ^ 2 * W + (-32768) * PowerSeries.X ^ 3 * G * T ^ 2 * W ^ 2 + (8192) * PowerSeries.X ^ 3 * G * T ^ 2 * W ^ 3 + (16384) * PowerSeries.X ^ 3 * G * T ^ 3 + (-24576) * PowerSeries.X ^ 3 * G * T ^ 3 * W + (8192) * PowerSeries.X ^ 3 * G * T ^ 3 * W ^ 2 + (-131072) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 + (196608) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 * W + (-98304) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 * W ^ 2 + (16384) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 * W ^ 3 + (-65536) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 3 + (131072) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 3 * W + (-81920) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 3 * W ^ 2 + (16384) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 3 * W ^ 3 + (-262144) * PowerSeries.X ^ 3 * G ^ 3 * T ^ 3 + (393216) * PowerSeries.X ^ 3 * G ^ 3 * T ^ 3 * W + (-196608) * PowerSeries.X ^ 3 * G ^ 3 * T ^ 3 * W ^ 2 + (32768) * PowerSeries.X ^ 3 * G ^ 3 * T ^ 3 * W ^ 3 + (16384) * PowerSeries.X ^ 4 + (-24576) * PowerSeries.X ^ 4 * W + (12288) * PowerSeries.X ^ 4 * W ^ 2 + (-2048) * PowerSeries.X ^ 4 * W ^ 3 + (-24576) * PowerSeries.X ^ 4 * T + (24576) * PowerSeries.X ^ 4 * T * W + (-6144) * PowerSeries.X ^ 4 * T * W ^ 2 + (12288) * PowerSeries.X ^ 4 * T ^ 2 + (-6144) * PowerSeries.X ^ 4 * T ^ 2 * W + (-2048) * PowerSeries.X ^ 4 * T ^ 3 + (32768) * PowerSeries.X ^ 4 * G * T + (-49152) * PowerSeries.X ^ 4 * G * T * W + (24576) * PowerSeries.X ^ 4 * G * T * W ^ 2 + (-4096) * PowerSeries.X ^ 4 * G * T * W ^ 3 + (-32768) * PowerSeries.X ^ 4 * G * T ^ 2 + (32768) * PowerSeries.X ^ 4 * G * T ^ 2 * W + (-8192) * PowerSeries.X ^ 4 * G * T ^ 2 * W ^ 2 + (8192) * PowerSeries.X ^ 4 * G * T ^ 3 + (-4096) * PowerSeries.X ^ 4 * G * T ^ 3 * W + (65536) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 + (-98304) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 * W + (49152) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 * W ^ 2 + (-8192) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 * W ^ 3 + (-32768) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 + (32768) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 * W + (-8192) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 * W ^ 2 + (131072) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 3 + (-196608) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 3 * W + (98304) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 3 * W ^ 2 + (-16384) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 3 * W ^ 3) * hG
  have hP : (4 * PowerSeries.X ^ 2 : PowerSeries ℚ) + (-2 + 8 * PowerSeries.X : PowerSeries ℚ) * G + (1 - 16 * PowerSeries.X + 48 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (12 - 112 * PowerSeries.X + 320 * PowerSeries.X ^ 2 - 256 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3 + (9 - 96 * PowerSeries.X + 352 * PowerSeries.X ^ 2 - 512 * PowerSeries.X ^ 3 + 256 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A268601Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A268601Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A268601Aux.rel G hP h0c m
      push_cast
      linear_combination r
