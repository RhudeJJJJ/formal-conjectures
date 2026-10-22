/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0028 : Family 7 := level7.get ⟨40,by decide⟩
def sourceMap0028 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0028 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0028_checked : acceptsGraphIso
    (source (graph core0028) (root 7) 2 2) DegreeOneMiddleResidualSpectrum074.graph sourceMap0028=true := by decide +kernel
theorem fusedMap0028_checked : acceptsGraphIso
    (fused (graph core0028) (root 7) 2 2) DegreeTwoThreeSpectrum1811.graph fusedMap0028=true := by decide +kernel
theorem certified0028 : Certified (graph core0028) (root 7) 2 2 :=
  of_native_maps core0028 DegreeOneMiddleResidualSpectrum074.graph DegreeTwoThreeSpectrum1811.graph
    sourceMap0028 fusedMap0028 sourceMap0028_checked fusedMap0028_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0028
#print axioms sourceMap0028_checked
#print axioms fusedMap0028_checked
#print axioms certified0028
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
