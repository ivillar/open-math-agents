import OMAStatements.S_arxiv_2611_01282
import Mathlib

-- Problem: arxiv-2611.01282, distinct covering systems with minimum moduli 8, 9, 10, 11 and least
-- common multiples 20160, 75600, 302400, 3326400 (Zhang, arXiv:2611.01282, Theorem 1).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The four residue lists are those of Appendix E of the source; the verification (bit masks
-- checked by the kernel) and the Lean proof are our own.

/-!
Theorem 1 of arXiv:2611.01282: the four residue lists of Appendix E of the source are distinct
covering systems with the stated minimum moduli and least common multiples. Coverage is checked
with bit masks: the class `a (mod d)` inside `[0, L)` has mask `2 ^ a * ((2 ^ L - 1) / (2 ^ d - 1))`,
and the bitwise or of all masks is `2 ^ L - 1`. Since every modulus divides `L`, coverage of
`[0, L)` gives coverage of all integers.
-/

namespace F2Cov

open OMA.S_arxiv_2611_01282

/-- Bit mask of the residue class `c.1 (mod c.2)` inside `[0, L)`. -/
def mask (L : ℕ) (c : ℕ × ℕ) : ℕ := 2 ^ c.1 * ((2 ^ L - 1) / (2 ^ c.2 - 1))

/-- Bitwise or of the masks of all classes of the list. -/
def orAll (L : ℕ) (l : List (ℕ × ℕ)) : ℕ := l.foldr (fun c acc => mask L c ||| acc) 0

/-- Least common multiple of the moduli of the list. -/
def lcmAll (l : List (ℕ × ℕ)) : ℕ := l.foldr (fun c acc => Nat.lcm c.2 acc) 1

theorem geom_bit (d : ℕ) (hd : 0 < d) : ∀ k i : ℕ,
    (∑ j ∈ Finset.range k, (2 ^ d) ^ j).testBit i = true → d ∣ i := by
  intro k
  induction k with
  | zero =>
    intro i h
    simp at h
  | succ k ih =>
    intro i h
    have h2 : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    have hlt : ∑ j ∈ Finset.range k, (2 ^ d) ^ j < 2 ^ (d * k) := by
      rw [pow_mul]
      exact Nat.geomSum_lt h2 (fun j hj => Finset.mem_range.mp hj)
    have e : ∑ j ∈ Finset.range (k + 1), (2 ^ d) ^ j =
        2 ^ (d * k) * 1 ||| ∑ j ∈ Finset.range k, (2 ^ d) ^ j := by
      rw [Finset.sum_range_succ, ← Nat.two_pow_add_eq_or_of_lt hlt 1, mul_one, pow_mul, add_comm]
    rw [e, Nat.testBit_or, mul_one, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨k, h.symm⟩
    · exact ih i h

theorem mask_bit (L : ℕ) (c : ℕ × ℕ) (n : ℕ) (hd : 0 < c.2) (hdL : c.2 ∣ L)
    (h : (mask L c).testBit n = true) : c.1 ≤ n ∧ c.2 ∣ n - c.1 := by
  unfold mask at h
  obtain ⟨k, rfl⟩ := hdL
  have h2 : 2 ≤ 2 ^ c.2 := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ c.2 := Nat.pow_le_pow_right (by norm_num) hd
  have e : (2 ^ (c.2 * k) - 1) / (2 ^ c.2 - 1) = ∑ j ∈ Finset.range k, (2 ^ c.2) ^ j := by
    rw [pow_mul]
    exact (Nat.geomSum_eq h2 k).symm
  rw [Nat.testBit_two_pow_mul, e, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, geom_bit c.2 hd k _ h.2⟩

theorem orAll_bit (L : ℕ) (n : ℕ) : ∀ l : List (ℕ × ℕ), (orAll L l).testBit n = true →
    ∃ c ∈ l, (mask L c).testBit n = true := by
  intro l
  induction l with
  | nil =>
    intro h
    simp [orAll] at h
  | cons c t ih =>
    intro h
    have e : orAll L (c :: t) = mask L c ||| orAll L t := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨c', hc', hb⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem c hc', hb⟩

theorem dvd_lcmAll : ∀ (l : List (ℕ × ℕ)) (c : ℕ × ℕ), c ∈ l → c.2 ∣ lcmAll l := by
  intro l
  induction l with
  | nil =>
    intro c hc
    simp at hc
  | cons a t ih =>
    intro c hc
    have e : lcmAll (a :: t) = Nat.lcm a.2 (lcmAll t) := rfl
    rw [e]
    rcases List.mem_cons.mp hc with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (ih c h).trans (Nat.dvd_lcm_right _ _)

theorem lcmAll_dvd : ∀ (l : List (ℕ × ℕ)) (k : ℕ), (∀ c ∈ l, c.2 ∣ k) → lcmAll l ∣ k := by
  intro l
  induction l with
  | nil =>
    intro k _
    exact one_dvd k
  | cons a t ih =>
    intro k h
    have e : lcmAll (a :: t) = Nat.lcm a.2 (lcmAll t) := rfl
    rw [e]
    exact Nat.lcm_dvd (h a List.mem_cons_self)
      (ih k (fun c hc => h c (List.mem_cons_of_mem a hc)))

theorem build (l : List (ℕ × ℕ)) (m L : ℕ) (hL : 0 < L)
    (hval : l.all (fun c => decide (2 ≤ c.2 ∧ c.1 < c.2)) = true)
    (hnd : (l.map Prod.snd).Nodup)
    (hlcm : lcmAll l = L)
    (hmin : (l.any (fun c => decide (c.2 = m)) && l.all (fun c => decide (m ≤ c.2))) = true)
    (hor : orAll L l = 2 ^ L - 1) :
    ∃ S : Finset (ℕ × ℕ), IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S m L := by
  have hv : ∀ c ∈ l, 2 ≤ c.2 ∧ c.1 < c.2 := by
    intro c hc
    have h := List.all_eq_true.mp hval c hc
    exact of_decide_eq_true h
  rw [Bool.and_eq_true] at hmin
  obtain ⟨hmin1, hmin2⟩ := hmin
  refine ⟨l.toFinset, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro c hc
    exact hv c (List.mem_toFinset.mp hc)
  · intro c hc c' hc' h
    exact List.inj_on_of_nodup_map hnd (List.mem_toFinset.mp hc) (List.mem_toFinset.mp hc') h
  · intro x
    have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = x % (L : ℤ) :=
      ⟨(x % (L : ℤ)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hLz.ne')⟩
    have hnL : n < L := by
      have h1 := Int.emod_lt_of_pos x hLz
      omega
    have hbit : (orAll L l).testBit n = true := by
      rw [hor, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hnL
    obtain ⟨c, hc, hcb⟩ := orAll_bit L n l hbit
    have hcv := hv c hc
    have hdL : c.2 ∣ L := by
      rw [← hlcm]
      exact dvd_lcmAll l c hc
    obtain ⟨han, hdn⟩ := mask_bit L c n (by omega) hdL hcb
    refine ⟨c, List.mem_toFinset.mpr hc, ?_⟩
    have h1 : x ≡ (n : ℤ) [ZMOD (L : ℤ)] := by
      rw [hn]
      exact (Int.mod_modEq x L).symm
    have h2 : x ≡ (n : ℤ) [ZMOD (c.2 : ℤ)] := h1.of_dvd (by exact_mod_cast hdL)
    have h3 : (n : ℤ) ≡ (c.1 : ℤ) [ZMOD (c.2 : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨t, ht⟩ := hdn
      refine ⟨-(t : ℤ), ?_⟩
      have h4 : (n : ℤ) - (c.1 : ℤ) = (c.2 : ℤ) * (t : ℤ) := by
        rw [← Nat.cast_sub han, ht, Nat.cast_mul]
      linarith
    exact h2.trans h3
  · obtain ⟨c, hc, hcm⟩ := List.any_eq_true.mp hmin1
    exact ⟨c, Finset.mem_coe.mpr (List.mem_toFinset.mpr hc), of_decide_eq_true hcm⟩
  · rintro d ⟨c, hc, rfl⟩
    have hc' := List.mem_toFinset.mp (Finset.mem_coe.mp hc)
    exact of_decide_eq_true (List.all_eq_true.mp hmin2 c hc')
  · rw [← hlcm]
    apply Nat.dvd_antisymm
    · exact Finset.lcm_dvd (fun c hc => dvd_lcmAll l c (List.mem_toFinset.mp hc))
    · exact lcmAll_dvd l _ (fun c hc => Finset.dvd_lcm (List.mem_toFinset.mpr hc))

/-- Appendix E.1 of the source: minimum modulus 8, least common multiple 20160. -/
def sys8 : List (ℕ × ℕ) :=
  [(3, 8), (8, 9), (6, 10), (1, 12), (2, 14), (3, 15), (7, 16), (2, 18), (0, 20), (19, 21),
    (9, 24), (10, 28), (12, 30), (15, 32), (34, 35), (29, 36), (10, 40), (22, 42), (23, 45),
    (21, 48), (46, 56), (24, 60), (28, 63), (63, 64), (14, 70), (41, 72), (77, 80), (4, 84),
    (32, 90), (45, 96), (13, 105), (52, 112), (30, 120), (112, 126), (54, 140), (5, 144),
    (61, 160), (136, 168), (104, 180), (159, 192), (202, 210), (95, 224), (189, 240), (70, 252),
    (74, 280), (77, 288), (239, 315), (287, 320), (220, 336), (230, 360), (414, 420), (415, 448),
    (285, 480), (466, 504), (18, 560), (479, 576), (448, 630), (127, 672), (365, 720),
    (790, 840), (95, 960), (298, 1008), (895, 1120), (952, 1260), (31, 1344), (509, 1440),
    (298, 1680), (1183, 2016), (671, 2240), (1642, 2520), (2399, 2880), (1631, 3360),
    (2527, 4032), (802, 5040), (2591, 6720), (7871, 10080), (6431, 20160)]

/-- Appendix E.2 of the source: minimum modulus 9, least common multiple 75600. -/
def sys9 : List (ℕ × ℕ) :=
  [(2, 9), (0, 10), (1, 12), (7, 14), (6, 15), (3, 16), (14, 18), (12, 20), (15, 21), (7, 24),
    (24, 25), (26, 27), (13, 28), (16, 30), (3, 35), (5, 36), (2, 40), (9, 42), (13, 45),
    (43, 48), (4, 50), (44, 54), (55, 56), (48, 60), (54, 63), (45, 70), (23, 72), (19, 75),
    (62, 80), (81, 84), (88, 90), (64, 100), (24, 105), (17, 108), (27, 112), (22, 120),
    (33, 126), (116, 135), (18, 140), (59, 144), (84, 150), (39, 168), (69, 175), (28, 180),
    (8, 189), (114, 200), (87, 210), (71, 216), (184, 225), (102, 240), (201, 252), (8, 270),
    (98, 280), (34, 300), (138, 315), (123, 336), (294, 350), (118, 360), (89, 378), (214, 400),
    (258, 420), (395, 432), (34, 450), (327, 504), (219, 525), (89, 540), (58, 560), (214, 600),
    (305, 630), (494, 675), (58, 700), (658, 720), (737, 756), (798, 840), (784, 900),
    (332, 945), (75, 1008), (144, 1050), (858, 1080), (414, 1200), (978, 1260), (1034, 1350),
    (198, 1400), (359, 1512), (1419, 1575), (538, 1680), (1278, 1800), (683, 1890), (618, 2100),
    (1142, 2160), (2458, 2520), (359, 2700), (338, 2800), (1115, 3024), (894, 3150), (978, 3600),
    (1817, 3780), (1038, 4200), (4679, 4725), (4618, 5040), (4814, 5400), (6078, 6300),
    (7487, 7560), (6498, 8400), (1439, 9450), (1979, 10800), (1878, 12600), (3707, 15120),
    (12239, 18900), (16578, 25200), (31679, 37800), (25423, 75600)]

/-- Appendix E.3 of the source: minimum modulus 10, least common multiple 302400. -/
def sys10 : List (ℕ × ℕ) :=
  [(8, 10), (9, 12), (4, 14), (5, 15), (7, 16), (13, 18), (2, 20), (17, 21), (3, 24), (24, 25),
    (25, 27), (8, 28), (0, 30), (31, 32), (21, 35), (1, 36), (32, 40), (5, 42), (10, 45),
    (35, 48), (14, 50), (43, 54), (20, 56), (6, 60), (62, 63), (47, 64), (26, 70), (19, 72),
    (59, 75), (12, 80), (29, 84), (40, 90), (11, 96), (54, 100), (86, 105), (61, 108),
    (100, 112), (96, 120), (41, 126), (115, 135), (106, 140), (125, 144), (84, 150), (132, 160),
    (137, 168), (119, 175), (173, 180), (115, 189), (15, 192), (104, 200), (16, 210), (115, 216),
    (123, 224), (109, 225), (17, 240), (77, 252), (70, 270), (216, 280), (155, 288), (294, 300),
    (146, 315), (212, 320), (53, 336), (194, 350), (317, 360), (178, 378), (204, 400),
    (286, 420), (341, 432), (180, 448), (184, 450), (143, 480), (149, 504), (44, 525),
    (413, 540), (156, 560), (271, 576), (144, 600), (346, 630), (155, 672), (259, 675),
    (694, 700), (137, 720), (10, 756), (4, 800), (276, 840), (485, 864), (29, 900), (451, 945),
    (527, 960), (221, 1008), (394, 1050), (593, 1080), (532, 1120), (689, 1200), (986, 1260),
    (1103, 1344), (34, 1350), (944, 1400), (923, 1440), (665, 1512), (1469, 1575), (404, 1600),
    (1577, 1680), (655, 1728), (389, 1800), (136, 1890), (1115, 2016), (1294, 2100), (197, 2160),
    (52, 2240), (239, 2400), (1913, 2520), (629, 2700), (44, 2800), (1403, 2880), (1673, 3024),
    (94, 3150), (3227, 3360), (1289, 3600), (2656, 3780), (539, 4032), (444, 4200), (3977, 4320),
    (4294, 4725), (1679, 4800), (1901, 5040), (5129, 5400), (5204, 5600), (917, 6048),
    (1994, 6300), (911, 6720), (2939, 7200), (233, 7560), (7289, 8400), (6137, 8640),
    (7444, 9450), (1787, 10080), (2789, 10800), (1204, 11200), (9557, 12096), (3929, 12600),
    (629, 14400), (7638, 15120), (13979, 16800), (1144, 18900), (11573, 20160), (16119, 21600),
    (23069, 25200), (9557, 30240), (10319, 33600), (12329, 37800), (22247, 43200),
    (25979, 50400), (45017, 60480), (54089, 75600), (50939, 100800), (47657, 151200),
    (63989, 302400)]

/-- Appendix E.4 of the source: minimum modulus 11, least common multiple 3326400. -/
def sys11 : List (ℕ × ℕ) :=
  [(10, 11), (9, 12), (12, 14), (10, 15), (7, 16), (11, 18), (16, 20), (4, 21), (6, 22), (3, 24),
    (17, 25), (26, 27), (2, 28), (1, 30), (31, 32), (14, 33), (34, 35), (5, 36), (8, 40),
    (18, 42), (2, 44), (19, 45), (36, 48), (2, 50), (17, 54), (9, 55), (22, 56), (13, 60),
    (7, 63), (28, 64), (8, 66), (48, 70), (59, 72), (7, 75), (45, 77), (64, 80), (42, 84),
    (18, 88), (49, 90), (15, 96), (11, 99), (12, 100), (73, 105), (89, 108), (20, 110),
    (106, 112), (43, 120), (112, 126), (38, 132), (34, 135), (6, 140), (95, 144), (127, 150),
    (136, 154), (108, 160), (125, 165), (150, 168), (97, 175), (84, 176), (0, 180), (106, 189),
    (60, 192), (176, 198), (32, 200), (90, 210), (35, 216), (60, 220), (162, 224), (172, 225),
    (158, 231), (24, 240), (154, 252), (62, 264), (259, 270), (97, 275), (268, 280), (204, 288),
    (143, 297), (37, 300), (210, 308), (304, 315), (204, 320), (320, 330), (234, 336), (62, 350),
    (172, 352), (240, 360), (187, 378), (224, 385), (86, 396), (272, 400), (346, 420),
    (143, 432), (40, 440), (274, 448), (247, 450), (452, 462), (463, 480), (218, 495),
    (436, 504), (262, 525), (68, 528), (300, 540), (522, 550), (184, 560), (498, 576), (44, 594),
    (187, 600), (92, 616), (94, 630), (200, 660), (66, 672), (547, 675), (56, 693), (482, 700),
    (700, 704), (104, 720), (232, 756), (114, 770), (716, 792), (332, 800), (482, 825),
    (148, 840), (696, 864), (148, 880), (72, 900), (686, 924), (79, 945), (684, 960), (416, 990),
    (738, 1008), (472, 1050), (332, 1056), (120, 1080), (262, 1100), (946, 1120), (254, 1155),
    (1142, 1188), (1087, 1200), (386, 1232), (904, 1260), (764, 1320), (498, 1344), (97, 1350),
    (980, 1386), (1072, 1400), (300, 1440), (1043, 1485), (66, 1512), (1148, 1540), (772, 1575),
    (200, 1584), (72, 1600), (632, 1650), (344, 1680), (1128, 1728), (1468, 1760), (1372, 1800),
    (1772, 1848), (394, 1890), (422, 1925), (1868, 1980), (402, 2016), (3, 2079), (2072, 2100),
    (1916, 2112), (480, 2160), (532, 2200), (498, 2240), (2174, 2310), (548, 2376), (562, 2400),
    (1170, 2464), (1672, 2475), (28, 2520), (104, 2640), (2172, 2700), (2350, 2772), (72, 2800),
    (562, 2880), (746, 2970), (24, 3024), (1624, 3080), (997, 3150), (1042, 3168), (2372, 3300),
    (274, 3360), (1767, 3465), (1202, 3520), (2172, 3600), (920, 3696), (1032, 3780),
    (1882, 3850), (3104, 3960), (3090, 4032), (3594, 4158), (672, 4200), (3720, 4320),
    (4072, 4400), (4412, 4620), (4497, 4725), (3432, 4752), (2099, 4800), (2034, 4928),
    (4092, 4950), (816, 5040), (3773, 5280), (4438, 5400), (2880, 5544), (4862, 5600),
    (336, 5775), (3146, 5940), (5041, 6048), (1904, 6160), (4036, 6300), (2721, 6336),
    (2556, 6600), (1010, 6720), (5897, 6930), (886, 7200), (7261, 7392), (5605, 7425),
    (3130, 7560), (1970, 7700), (774, 7920), (6649, 8316), (5839, 8400), (5981, 8640),
    (4689, 8800), (4243, 9240), (7730, 9450), (1719, 9504), (7105, 9900), (6726, 10080),
    (6187, 10395), (8945, 10560), (4943, 10800), (3786, 11088), (5044, 11200), (3673, 11550),
    (9926, 11880), (10181, 12096), (1274, 12320), (8343, 12600), (10026, 13200), (11411, 13860),
    (2011, 14400), (1552, 14784), (8389, 14850), (2510, 15120), (15235, 15400), (14188, 15840),
    (15253, 16632), (10805, 16800), (1288, 17325), (1272, 17600), (5039, 18480), (11887, 18900),
    (979, 19008), (17429, 19800), (15730, 20160), (12921, 20790), (6032, 21600), (17906, 22176),
    (2771, 23100), (3380, 23760), (23285, 24640), (17262, 25200), (23334, 26400), (20944, 27720),
    (22244, 29700), (7550, 30240), (7822, 30800), (5560, 31680), (27480, 33264), (4057, 33600),
    (28859, 34650), (24257, 36960), (27555, 37800), (6931, 39600), (7422, 41580), (26748, 43200),
    (117, 44352), (14953, 46200), (12869, 47520), (35, 50400), (43386, 51975), (21190, 52800),
    (8832, 55440), (28604, 59400), (51290, 60480), (2316, 61600), (8436, 66528), (33019, 69300),
    (65340, 73920), (36658, 75600), (33041, 79200), (9471, 83160), (16431, 92400),
    (18516, 95040), (6783, 100800), (91813, 103950), (60518, 110880), (59889, 118800),
    (3696, 123200), (62596, 133056), (87874, 138600), (116975, 151200), (34401, 158400),
    (90791, 166320), (53591, 184800), (147882, 207900), (62786, 221760), (197451, 237600),
    (86741, 277200), (64669, 302400), (173009, 332640), (295599, 369600), (47173, 415800),
    (225747, 475200), (414022, 554400), (25865, 665280), (110190, 831600), (1031743, 1108800),
    (1097511, 1663200), (1956368, 3326400)]

theorem v8 : sys8.all (fun c => decide (2 ≤ c.2 ∧ c.1 < c.2)) = true := by decide +kernel

theorem n8 : (sys8.map Prod.snd).Nodup := by decide +kernel

theorem l8 : lcmAll sys8 = 20160 := by decide +kernel

theorem m8 : (sys8.any (fun c => decide (c.2 = 8)) &&
    sys8.all (fun c => decide (8 ≤ c.2))) = true := by decide +kernel

theorem o8 : orAll 20160 sys8 = 2 ^ 20160 - 1 := by decide +kernel

theorem cover8 : ∃ S : Finset (ℕ × ℕ),
    IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 8 20160 :=
  build sys8 8 20160 (by norm_num) v8 n8 l8 m8 o8

theorem v9 : sys9.all (fun c => decide (2 ≤ c.2 ∧ c.1 < c.2)) = true := by decide +kernel

theorem n9 : (sys9.map Prod.snd).Nodup := by decide +kernel

theorem l9 : lcmAll sys9 = 75600 := by decide +kernel

theorem m9 : (sys9.any (fun c => decide (c.2 = 9)) &&
    sys9.all (fun c => decide (9 ≤ c.2))) = true := by decide +kernel

theorem o9 : orAll 75600 sys9 = 2 ^ 75600 - 1 := by decide +kernel

theorem cover9 : ∃ S : Finset (ℕ × ℕ),
    IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 9 75600 :=
  build sys9 9 75600 (by norm_num) v9 n9 l9 m9 o9

theorem v10 : sys10.all (fun c => decide (2 ≤ c.2 ∧ c.1 < c.2)) = true := by decide +kernel

theorem n10 : (sys10.map Prod.snd).Nodup := by decide +kernel

theorem l10 : lcmAll sys10 = 302400 := by decide +kernel

theorem m10 : (sys10.any (fun c => decide (c.2 = 10)) &&
    sys10.all (fun c => decide (10 ≤ c.2))) = true := by decide +kernel

theorem o10 : orAll 302400 sys10 = 2 ^ 302400 - 1 := by decide +kernel

theorem cover10 : ∃ S : Finset (ℕ × ℕ),
    IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 10 302400 :=
  build sys10 10 302400 (by norm_num) v10 n10 l10 m10 o10

theorem v11 : sys11.all (fun c => decide (2 ≤ c.2 ∧ c.1 < c.2)) = true := by decide +kernel

theorem n11 : (sys11.map Prod.snd).Nodup := by decide +kernel

theorem l11 : lcmAll sys11 = 3326400 := by decide +kernel

theorem m11 : (sys11.any (fun c => decide (c.2 = 11)) &&
    sys11.all (fun c => decide (11 ≤ c.2))) = true := by decide +kernel

theorem o11 : orAll 3326400 sys11 = 2 ^ 3326400 - 1 := by decide +kernel

theorem cover11 : ∃ S : Finset (ℕ × ℕ),
    IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 11 3326400 :=
  build sys11 11 3326400 (by norm_num) v11 n11 l11 m11 o11

end F2Cov

theorem OMA.solution : type_of% @OMA.S_arxiv_2611_01282.main :=
  ⟨F2Cov.cover8, F2Cov.cover9, F2Cov.cover10, F2Cov.cover11⟩
