/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4546 : Family 10 := level10.get ⟨441,by decide⟩
def sourceMap4546 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4546 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4546_checked : acceptsGraphIso
    (source (graph core4546) (root 10) 2 2) DegreeTwoThreeSpectrum6851.graph sourceMap4546=true := by decide +kernel
theorem fusedMap4546_checked : acceptsGraphIso
    (fused (graph core4546) (root 10) 2 2) DegreeTwoThreeSpectrum5856.graph fusedMap4546=true := by decide +kernel
theorem certified4546 : Certified (graph core4546) (root 10) 2 2 :=
  of_native_maps core4546 DegreeTwoThreeSpectrum6851.graph DegreeTwoThreeSpectrum5856.graph
    sourceMap4546 fusedMap4546 sourceMap4546_checked fusedMap4546_checked
    DegreeTwoThreeFiniteComparisons.comparison4546
#print axioms sourceMap4546_checked
#print axioms fusedMap4546_checked
#print axioms certified4546
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
