/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0252 : Family 9 := level9.get ⟨70,by decide⟩
def sourceMap0252 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0252 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0252_checked : acceptsGraphIso
    (source (graph core0252) (root 9) 2 2) DegreeOneMiddleResidualSpectrum650.graph sourceMap0252=true := by decide +kernel
theorem fusedMap0252_checked : acceptsGraphIso
    (fused (graph core0252) (root 9) 2 2) DegreeTwoThreeSpectrum3991.graph fusedMap0252=true := by decide +kernel
theorem certified0252 : Certified (graph core0252) (root 9) 2 2 :=
  of_native_maps core0252 DegreeOneMiddleResidualSpectrum650.graph DegreeTwoThreeSpectrum3991.graph
    sourceMap0252 fusedMap0252 sourceMap0252_checked fusedMap0252_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0252
#print axioms sourceMap0252_checked
#print axioms fusedMap0252_checked
#print axioms certified0252
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
