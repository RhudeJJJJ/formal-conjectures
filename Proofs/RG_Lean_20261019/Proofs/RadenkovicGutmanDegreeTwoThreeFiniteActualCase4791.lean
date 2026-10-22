/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4791 : Family 10 := level10.get ⟨1111,by decide⟩
def sourceMap4791 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4791 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4791_checked : acceptsGraphIso
    (source (graph core4791) (root 10) 2 2) DegreeTwoThreeSpectrum7191.graph sourceMap4791=true := by decide +kernel
theorem fusedMap4791_checked : acceptsGraphIso
    (fused (graph core4791) (root 10) 2 2) DegreeTwoThreeSpectrum6208.graph fusedMap4791=true := by decide +kernel
theorem certified4791 : Certified (graph core4791) (root 10) 2 2 :=
  of_native_maps core4791 DegreeTwoThreeSpectrum7191.graph DegreeTwoThreeSpectrum6208.graph
    sourceMap4791 fusedMap4791 sourceMap4791_checked fusedMap4791_checked
    DegreeTwoThreeFiniteComparisons.comparison4791
#print axioms sourceMap4791_checked
#print axioms fusedMap4791_checked
#print axioms certified4791
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
