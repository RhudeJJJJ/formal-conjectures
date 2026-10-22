/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0732 : Family 10 := level10.get ⟨356,by decide⟩
def sourceMap0732 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0732 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0732_checked : acceptsGraphIso
    (source (graph core0732) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1824.graph sourceMap0732=true := by decide +kernel
theorem fusedMap0732_checked : acceptsGraphIso
    (fused (graph core0732) (root 10) 2 2) DegreeTwoThreeSpectrum5637.graph fusedMap0732=true := by decide +kernel
theorem certified0732 : Certified (graph core0732) (root 10) 2 2 :=
  of_native_maps core0732 DegreeOneMiddleResidualSpectrum1824.graph DegreeTwoThreeSpectrum5637.graph
    sourceMap0732 fusedMap0732 sourceMap0732_checked fusedMap0732_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0732
#print axioms sourceMap0732_checked
#print axioms fusedMap0732_checked
#print axioms certified0732
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
