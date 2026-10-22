/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0854 : Family 10 := level10.get ⟨582,by decide⟩
def sourceMap0854 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0854 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0854_checked : acceptsGraphIso
    (source (graph core0854) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2076.graph sourceMap0854=true := by decide +kernel
theorem fusedMap0854_checked : acceptsGraphIso
    (fused (graph core0854) (root 10) 2 2) DegreeTwoThreeSpectrum5251.graph fusedMap0854=true := by decide +kernel
theorem certified0854 : Certified (graph core0854) (root 10) 2 2 :=
  of_native_maps core0854 DegreeOneMiddleResidualSpectrum2076.graph DegreeTwoThreeSpectrum5251.graph
    sourceMap0854 fusedMap0854 sourceMap0854_checked fusedMap0854_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0854
#print axioms sourceMap0854_checked
#print axioms fusedMap0854_checked
#print axioms certified0854
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
