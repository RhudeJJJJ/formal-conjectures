/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0962 : Family 10 := level10.get ⟨1603,by decide⟩
def sourceMap0962 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0962 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0962_checked : acceptsGraphIso
    (source (graph core0962) (root 10) 0 0) DegreeTwoThreeSpectrum1469.graph sourceMap0962=true := by decide +kernel
theorem fusedMap0962_checked : acceptsGraphIso
    (fused (graph core0962) (root 10) 0 0) DegreeTwoThreeSpectrum1468.graph fusedMap0962=true := by decide +kernel
theorem certified0962 : Certified (graph core0962) (root 10) 0 0 :=
  of_native_maps core0962 DegreeTwoThreeSpectrum1469.graph DegreeTwoThreeSpectrum1468.graph
    sourceMap0962 fusedMap0962 sourceMap0962_checked fusedMap0962_checked
    DegreeTwoThreeFiniteComparisons.comparison0962
#print axioms sourceMap0962_checked
#print axioms fusedMap0962_checked
#print axioms certified0962
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
