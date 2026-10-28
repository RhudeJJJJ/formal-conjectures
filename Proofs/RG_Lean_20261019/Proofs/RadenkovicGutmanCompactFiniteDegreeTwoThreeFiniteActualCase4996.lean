/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4996 : Family 10 := level10.get ⟨1607,by decide⟩
def sourceMap4996 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,12,13,14,15,16,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4996 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4996_checked : acceptsGraphIso
    (source (graph core4996) (root 10) 2 2) DegreeTwoThreeSpectrum7597.graph sourceMap4996=true := by decide +kernel
theorem fusedMap4996_checked : acceptsGraphIso
    (fused (graph core4996) (root 10) 2 2) DegreeTwoThreeSpectrum6126.graph fusedMap4996=true := by decide +kernel
theorem certified4996 : Certified (graph core4996) (root 10) 2 2 :=
  of_native_maps core4996 DegreeTwoThreeSpectrum7597.graph DegreeTwoThreeSpectrum6126.graph
    sourceMap4996 fusedMap4996 sourceMap4996_checked fusedMap4996_checked
    DegreeTwoThreeFiniteComparisons.comparison4996
#print axioms sourceMap4996_checked
#print axioms fusedMap4996_checked
#print axioms certified4996
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
