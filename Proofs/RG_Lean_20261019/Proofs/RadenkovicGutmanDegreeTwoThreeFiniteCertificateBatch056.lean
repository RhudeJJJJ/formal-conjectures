/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2800
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2801
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2802
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2803
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2804
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2805
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2806
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2807
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2808
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2809
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2810
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2811
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2812
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2813
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2814
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2815
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2816
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2817
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2818
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2819
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2820
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2821
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2822
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2823
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2824
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2825
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2826
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2827
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2828
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2829
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2830
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2831
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2832
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2833
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2834
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2835
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2836
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2837
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2838
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2839
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2840
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2841
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2842
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2843
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2844
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2845
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2846
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2847
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2848
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2849
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys056 : ∀ k ∈ keys056, Certified k := by
  apply certified_cons (by exact certified2800)
  apply certified_cons (by exact certified2800swap)
  apply certified_cons (by exact certified2801)
  apply certified_cons (by exact certified2801swap)
  apply certified_cons (by exact certified2802)
  apply certified_cons (by exact certified2802swap)
  apply certified_cons (by exact certified2803)
  apply certified_cons (by exact certified2803swap)
  apply certified_cons (by exact certified2804)
  apply certified_cons (by exact certified2804swap)
  apply certified_cons (by exact certified2805)
  apply certified_cons (by exact certified2805swap)
  apply certified_cons (by exact certified2806)
  apply certified_cons (by exact certified2806swap)
  apply certified_cons (by exact certified2807)
  apply certified_cons (by exact certified2807swap)
  apply certified_cons (by exact certified2808)
  apply certified_cons (by exact certified2808swap)
  apply certified_cons (by exact certified2809)
  apply certified_cons (by exact certified2809swap)
  apply certified_cons (by exact certified2810)
  apply certified_cons (by exact certified2810swap)
  apply certified_cons (by exact certified2811)
  apply certified_cons (by exact certified2811swap)
  apply certified_cons (by exact certified2812)
  apply certified_cons (by exact certified2812swap)
  apply certified_cons (by exact certified2813)
  apply certified_cons (by exact certified2813swap)
  apply certified_cons (by exact certified2814)
  apply certified_cons (by exact certified2814swap)
  apply certified_cons (by exact certified2815)
  apply certified_cons (by exact certified2815swap)
  apply certified_cons (by exact certified2816)
  apply certified_cons (by exact certified2816swap)
  apply certified_cons (by exact certified2817)
  apply certified_cons (by exact certified2817swap)
  apply certified_cons (by exact certified2818)
  apply certified_cons (by exact certified2818swap)
  apply certified_cons (by exact certified2819)
  apply certified_cons (by exact certified2819swap)
  apply certified_cons (by exact certified2820)
  apply certified_cons (by exact certified2820swap)
  apply certified_cons (by exact certified2821)
  apply certified_cons (by exact certified2821swap)
  apply certified_cons (by exact certified2822)
  apply certified_cons (by exact certified2822swap)
  apply certified_cons (by exact certified2823)
  apply certified_cons (by exact certified2823swap)
  apply certified_cons (by exact certified2824)
  apply certified_cons (by exact certified2824swap)
  apply certified_cons (by exact certified2825)
  apply certified_cons (by exact certified2825swap)
  apply certified_cons (by exact certified2826)
  apply certified_cons (by exact certified2826swap)
  apply certified_cons (by exact certified2827)
  apply certified_cons (by exact certified2827swap)
  apply certified_cons (by exact certified2828)
  apply certified_cons (by exact certified2828swap)
  apply certified_cons (by exact certified2829)
  apply certified_cons (by exact certified2829swap)
  apply certified_cons (by exact certified2830)
  apply certified_cons (by exact certified2830swap)
  apply certified_cons (by exact certified2831)
  apply certified_cons (by exact certified2831swap)
  apply certified_cons (by exact certified2832)
  apply certified_cons (by exact certified2832swap)
  apply certified_cons (by exact certified2833)
  apply certified_cons (by exact certified2833swap)
  apply certified_cons (by exact certified2834)
  apply certified_cons (by exact certified2834swap)
  apply certified_cons (by exact certified2835)
  apply certified_cons (by exact certified2835swap)
  apply certified_cons (by exact certified2836)
  apply certified_cons (by exact certified2836swap)
  apply certified_cons (by exact certified2837)
  apply certified_cons (by exact certified2837swap)
  apply certified_cons (by exact certified2838)
  apply certified_cons (by exact certified2838swap)
  apply certified_cons (by exact certified2839)
  apply certified_cons (by exact certified2839swap)
  apply certified_cons (by exact certified2840)
  apply certified_cons (by exact certified2840swap)
  apply certified_cons (by exact certified2841)
  apply certified_cons (by exact certified2841swap)
  apply certified_cons (by exact certified2842)
  apply certified_cons (by exact certified2842swap)
  apply certified_cons (by exact certified2843)
  apply certified_cons (by exact certified2843swap)
  apply certified_cons (by exact certified2844)
  apply certified_cons (by exact certified2844swap)
  apply certified_cons (by exact certified2845)
  apply certified_cons (by exact certified2845swap)
  apply certified_cons (by exact certified2846)
  apply certified_cons (by exact certified2846swap)
  apply certified_cons (by exact certified2847)
  apply certified_cons (by exact certified2847swap)
  apply certified_cons (by exact certified2848)
  apply certified_cons (by exact certified2848swap)
  apply certified_cons (by exact certified2849)
  apply certified_cons (by exact certified2849swap)
  simp
#print axioms certified_keys056
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
