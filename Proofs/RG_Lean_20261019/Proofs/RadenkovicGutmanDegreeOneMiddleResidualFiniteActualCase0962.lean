/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0962 : Family 10 := level10.get ⟨801,by decide⟩
def sourceMap0962 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0962 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0962_checked : acceptsGraphIso
    (source (graph core0962) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2250.graph sourceMap0962=true := by decide +kernel
theorem fusedMap0962_checked : acceptsGraphIso
    (fused (graph core0962) (root 10) 2 2) DegreeTwoThreeSpectrum5597.graph fusedMap0962=true := by decide +kernel
theorem certified0962 : Certified (graph core0962) (root 10) 2 2 :=
  of_native_maps core0962 DegreeOneMiddleResidualSpectrum2250.graph DegreeTwoThreeSpectrum5597.graph
    sourceMap0962 fusedMap0962 sourceMap0962_checked fusedMap0962_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0962
#print axioms sourceMap0962_checked
#print axioms fusedMap0962_checked
#print axioms certified0962
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
