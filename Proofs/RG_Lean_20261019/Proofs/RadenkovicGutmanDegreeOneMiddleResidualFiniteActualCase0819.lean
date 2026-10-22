/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0819 : Family 10 := level10.get ⟨522,by decide⟩
def sourceMap0819 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0819 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0819_checked : acceptsGraphIso
    (source (graph core0819) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2006.graph sourceMap0819=true := by decide +kernel
theorem fusedMap0819_checked : acceptsGraphIso
    (fused (graph core0819) (root 10) 2 2) DegreeTwoThreeSpectrum5165.graph fusedMap0819=true := by decide +kernel
theorem certified0819 : Certified (graph core0819) (root 10) 2 2 :=
  of_native_maps core0819 DegreeOneMiddleResidualSpectrum2006.graph DegreeTwoThreeSpectrum5165.graph
    sourceMap0819 fusedMap0819 sourceMap0819_checked fusedMap0819_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0819
#print axioms sourceMap0819_checked
#print axioms fusedMap0819_checked
#print axioms certified0819
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
