/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0017 : Family 7 := level7.get ⟨21,by decide⟩
def sourceMap0017 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0017 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0017_checked : acceptsGraphIso
    (source (graph core0017) (root 7) 2 2) DegreeTwoThreeSpectrum2189.graph sourceMap0017=true := by decide +kernel
theorem fusedMap0017_checked : acceptsGraphIso
    (fused (graph core0017) (root 7) 2 2) DegreeTwoThreeSpectrum1729.graph fusedMap0017=true := by decide +kernel
theorem certified0017 : Certified (graph core0017) (root 7) 2 2 :=
  of_native_maps core0017 DegreeTwoThreeSpectrum2189.graph DegreeTwoThreeSpectrum1729.graph
    sourceMap0017 fusedMap0017 sourceMap0017_checked fusedMap0017_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0017
#print axioms sourceMap0017_checked
#print axioms fusedMap0017_checked
#print axioms certified0017
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
