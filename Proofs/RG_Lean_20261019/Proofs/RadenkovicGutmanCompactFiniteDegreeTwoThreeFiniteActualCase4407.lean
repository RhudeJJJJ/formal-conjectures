/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4407 : Family 9 := level9.get ⟨609,by decide⟩
def sourceMap4407 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4407 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4407_checked : acceptsGraphIso
    (source (graph core4407) (root 9) 2 2) DegreeTwoThreeSpectrum4934.graph sourceMap4407=true := by decide +kernel
theorem fusedMap4407_checked : acceptsGraphIso
    (fused (graph core4407) (root 9) 2 2) DegreeTwoThreeSpectrum4304.graph fusedMap4407=true := by decide +kernel
theorem certified4407 : Certified (graph core4407) (root 9) 2 2 :=
  of_native_maps core4407 DegreeTwoThreeSpectrum4934.graph DegreeTwoThreeSpectrum4304.graph
    sourceMap4407 fusedMap4407 sourceMap4407_checked fusedMap4407_checked
    DegreeTwoThreeFiniteComparisons.comparison4407
#print axioms sourceMap4407_checked
#print axioms fusedMap4407_checked
#print axioms certified4407
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
