/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4411 : Family 9 := level9.get ⟨622,by decide⟩
def sourceMap4411 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,11,12,13,14,15,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4411 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4411_checked : acceptsGraphIso
    (source (graph core4411) (root 9) 2 2) DegreeTwoThreeSpectrum4938.graph sourceMap4411=true := by decide +kernel
theorem fusedMap4411_checked : acceptsGraphIso
    (fused (graph core4411) (root 9) 2 2) DegreeTwoThreeSpectrum4339.graph fusedMap4411=true := by decide +kernel
theorem certified4411 : Certified (graph core4411) (root 9) 2 2 :=
  of_native_maps core4411 DegreeTwoThreeSpectrum4938.graph DegreeTwoThreeSpectrum4339.graph
    sourceMap4411 fusedMap4411 sourceMap4411_checked fusedMap4411_checked
    DegreeTwoThreeFiniteComparisons.comparison4411
#print axioms sourceMap4411_checked
#print axioms fusedMap4411_checked
#print axioms certified4411
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
