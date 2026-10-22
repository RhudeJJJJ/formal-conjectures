/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2950
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2951
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2952
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2953
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2954
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2955
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2956
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2957
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2958
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2959
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2960
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2961
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2962
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2963
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2964
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2965
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2966
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2967
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2968
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2969
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2970
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2971
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2972
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2973
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2974
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2975
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2976
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2977
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2978
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2979
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2980
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2981
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2982
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2983
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2984
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2985
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2986
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2987
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2988
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2989
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2990
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2991
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2992
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2993
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2994
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2995
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2996
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2997
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2998
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2999
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys059 : ∀ k ∈ keys059, Certified k := by
  apply certified_cons (by exact certified2950)
  apply certified_cons (by exact certified2950swap)
  apply certified_cons (by exact certified2951)
  apply certified_cons (by exact certified2951swap)
  apply certified_cons (by exact certified2952)
  apply certified_cons (by exact certified2952swap)
  apply certified_cons (by exact certified2953)
  apply certified_cons (by exact certified2953swap)
  apply certified_cons (by exact certified2954)
  apply certified_cons (by exact certified2954swap)
  apply certified_cons (by exact certified2955)
  apply certified_cons (by exact certified2955swap)
  apply certified_cons (by exact certified2956)
  apply certified_cons (by exact certified2956swap)
  apply certified_cons (by exact certified2957)
  apply certified_cons (by exact certified2957swap)
  apply certified_cons (by exact certified2958)
  apply certified_cons (by exact certified2958swap)
  apply certified_cons (by exact certified2959)
  apply certified_cons (by exact certified2959swap)
  apply certified_cons (by exact certified2960)
  apply certified_cons (by exact certified2960swap)
  apply certified_cons (by exact certified2961)
  apply certified_cons (by exact certified2961swap)
  apply certified_cons (by exact certified2962)
  apply certified_cons (by exact certified2962swap)
  apply certified_cons (by exact certified2963)
  apply certified_cons (by exact certified2963swap)
  apply certified_cons (by exact certified2964)
  apply certified_cons (by exact certified2964swap)
  apply certified_cons (by exact certified2965)
  apply certified_cons (by exact certified2965swap)
  apply certified_cons (by exact certified2966)
  apply certified_cons (by exact certified2966swap)
  apply certified_cons (by exact certified2967)
  apply certified_cons (by exact certified2967swap)
  apply certified_cons (by exact certified2968)
  apply certified_cons (by exact certified2968swap)
  apply certified_cons (by exact certified2969)
  apply certified_cons (by exact certified2969swap)
  apply certified_cons (by exact certified2970)
  apply certified_cons (by exact certified2970swap)
  apply certified_cons (by exact certified2971)
  apply certified_cons (by exact certified2971swap)
  apply certified_cons (by exact certified2972)
  apply certified_cons (by exact certified2972swap)
  apply certified_cons (by exact certified2973)
  apply certified_cons (by exact certified2973swap)
  apply certified_cons (by exact certified2974)
  apply certified_cons (by exact certified2974swap)
  apply certified_cons (by exact certified2975)
  apply certified_cons (by exact certified2975swap)
  apply certified_cons (by exact certified2976)
  apply certified_cons (by exact certified2976swap)
  apply certified_cons (by exact certified2977)
  apply certified_cons (by exact certified2977swap)
  apply certified_cons (by exact certified2978)
  apply certified_cons (by exact certified2978swap)
  apply certified_cons (by exact certified2979)
  apply certified_cons (by exact certified2979swap)
  apply certified_cons (by exact certified2980)
  apply certified_cons (by exact certified2980swap)
  apply certified_cons (by exact certified2981)
  apply certified_cons (by exact certified2981swap)
  apply certified_cons (by exact certified2982)
  apply certified_cons (by exact certified2982swap)
  apply certified_cons (by exact certified2983)
  apply certified_cons (by exact certified2983swap)
  apply certified_cons (by exact certified2984)
  apply certified_cons (by exact certified2984swap)
  apply certified_cons (by exact certified2985)
  apply certified_cons (by exact certified2985swap)
  apply certified_cons (by exact certified2986)
  apply certified_cons (by exact certified2986swap)
  apply certified_cons (by exact certified2987)
  apply certified_cons (by exact certified2987swap)
  apply certified_cons (by exact certified2988)
  apply certified_cons (by exact certified2988swap)
  apply certified_cons (by exact certified2989)
  apply certified_cons (by exact certified2989swap)
  apply certified_cons (by exact certified2990)
  apply certified_cons (by exact certified2990swap)
  apply certified_cons (by exact certified2991)
  apply certified_cons (by exact certified2991swap)
  apply certified_cons (by exact certified2992)
  apply certified_cons (by exact certified2992swap)
  apply certified_cons (by exact certified2993)
  apply certified_cons (by exact certified2993swap)
  apply certified_cons (by exact certified2994)
  apply certified_cons (by exact certified2994swap)
  apply certified_cons (by exact certified2995)
  apply certified_cons (by exact certified2995swap)
  apply certified_cons (by exact certified2996)
  apply certified_cons (by exact certified2996swap)
  apply certified_cons (by exact certified2997)
  apply certified_cons (by exact certified2997swap)
  apply certified_cons (by exact certified2998)
  apply certified_cons (by exact certified2998swap)
  apply certified_cons (by exact certified2999)
  apply certified_cons (by exact certified2999swap)
  simp
#print axioms certified_keys059
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
