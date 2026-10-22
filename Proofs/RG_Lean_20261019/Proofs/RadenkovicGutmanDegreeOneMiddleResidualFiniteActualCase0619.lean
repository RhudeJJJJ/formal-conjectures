/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0619 : Family 10 := level10.get ⟨179,by decide⟩
def sourceMap0619 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,9,10,11,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0619 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0619_checked : acceptsGraphIso
    (source (graph core0619) (root 10) 2 2) DegreeTwoThreeSpectrum6862.graph sourceMap0619=true := by decide +kernel
theorem fusedMap0619_checked : acceptsGraphIso
    (fused (graph core0619) (root 10) 2 2) DegreeTwoThreeSpectrum5126.graph fusedMap0619=true := by decide +kernel
theorem certified0619 : Certified (graph core0619) (root 10) 2 2 :=
  of_native_maps core0619 DegreeTwoThreeSpectrum6862.graph DegreeTwoThreeSpectrum5126.graph
    sourceMap0619 fusedMap0619 sourceMap0619_checked fusedMap0619_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0619
#print axioms sourceMap0619_checked
#print axioms fusedMap0619_checked
#print axioms certified0619
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
