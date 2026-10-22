/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0856 : Family 10 := level10.get ⟨585,by decide⟩
def sourceMap0856 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0856 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0856_checked : acceptsGraphIso
    (source (graph core0856) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2078.graph sourceMap0856=true := by decide +kernel
theorem fusedMap0856_checked : acceptsGraphIso
    (fused (graph core0856) (root 10) 2 2) DegreeTwoThreeSpectrum5255.graph fusedMap0856=true := by decide +kernel
theorem certified0856 : Certified (graph core0856) (root 10) 2 2 :=
  of_native_maps core0856 DegreeOneMiddleResidualSpectrum2078.graph DegreeTwoThreeSpectrum5255.graph
    sourceMap0856 fusedMap0856 sourceMap0856_checked fusedMap0856_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0856
#print axioms sourceMap0856_checked
#print axioms fusedMap0856_checked
#print axioms certified0856
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
