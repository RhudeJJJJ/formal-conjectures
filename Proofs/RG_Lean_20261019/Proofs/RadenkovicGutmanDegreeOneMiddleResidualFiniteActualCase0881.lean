/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0881 : Family 10 := level10.get ⟨629,by decide⟩
def sourceMap0881 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0881 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0881_checked : acceptsGraphIso
    (source (graph core0881) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2123.graph sourceMap0881=true := by decide +kernel
theorem fusedMap0881_checked : acceptsGraphIso
    (fused (graph core0881) (root 10) 2 2) DegreeTwoThreeSpectrum5320.graph fusedMap0881=true := by decide +kernel
theorem certified0881 : Certified (graph core0881) (root 10) 2 2 :=
  of_native_maps core0881 DegreeOneMiddleResidualSpectrum2123.graph DegreeTwoThreeSpectrum5320.graph
    sourceMap0881 fusedMap0881 sourceMap0881_checked fusedMap0881_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0881
#print axioms sourceMap0881_checked
#print axioms fusedMap0881_checked
#print axioms certified0881
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
