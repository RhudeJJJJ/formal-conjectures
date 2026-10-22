/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0877 : Family 10 := level10.get ⟨624,by decide⟩
def sourceMap0877 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0877 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0877_checked : acceptsGraphIso
    (source (graph core0877) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2118.graph sourceMap0877=true := by decide +kernel
theorem fusedMap0877_checked : acceptsGraphIso
    (fused (graph core0877) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1181.graph fusedMap0877=true := by decide +kernel
theorem certified0877 : Certified (graph core0877) (root 10) 2 2 :=
  of_native_maps core0877 DegreeOneMiddleResidualSpectrum2118.graph DegreeOneMiddleResidualSpectrum1181.graph
    sourceMap0877 fusedMap0877 sourceMap0877_checked fusedMap0877_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0877
#print axioms sourceMap0877_checked
#print axioms fusedMap0877_checked
#print axioms certified0877
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
