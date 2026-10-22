/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0527 : Family 10 := level10.get ⟨53,by decide⟩
def sourceMap0527 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0527 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0527_checked : acceptsGraphIso
    (source (graph core0527) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1543.graph sourceMap0527=true := by decide +kernel
theorem fusedMap0527_checked : acceptsGraphIso
    (fused (graph core0527) (root 10) 2 2) DegreeOneMiddleResidualSpectrum936.graph fusedMap0527=true := by decide +kernel
theorem certified0527 : Certified (graph core0527) (root 10) 2 2 :=
  of_native_maps core0527 DegreeOneMiddleResidualSpectrum1543.graph DegreeOneMiddleResidualSpectrum936.graph
    sourceMap0527 fusedMap0527 sourceMap0527_checked fusedMap0527_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0527
#print axioms sourceMap0527_checked
#print axioms fusedMap0527_checked
#print axioms certified0527
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
