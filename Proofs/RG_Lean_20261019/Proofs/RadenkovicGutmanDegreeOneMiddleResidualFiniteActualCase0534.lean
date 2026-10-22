/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0534 : Family 10 := level10.get ⟨61,by decide⟩
def sourceMap0534 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0534 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0534_checked : acceptsGraphIso
    (source (graph core0534) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1633.graph sourceMap0534=true := by decide +kernel
theorem fusedMap0534_checked : acceptsGraphIso
    (fused (graph core0534) (root 10) 2 2) DegreeTwoThreeSpectrum4974.graph fusedMap0534=true := by decide +kernel
theorem certified0534 : Certified (graph core0534) (root 10) 2 2 :=
  of_native_maps core0534 DegreeOneMiddleResidualSpectrum1633.graph DegreeTwoThreeSpectrum4974.graph
    sourceMap0534 fusedMap0534 sourceMap0534_checked fusedMap0534_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0534
#print axioms sourceMap0534_checked
#print axioms fusedMap0534_checked
#print axioms certified0534
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
