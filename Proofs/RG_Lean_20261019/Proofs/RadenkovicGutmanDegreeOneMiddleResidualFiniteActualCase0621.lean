/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0621 : Family 10 := level10.get ⟨189,by decide⟩
def sourceMap0621 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0621 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0621_checked : acceptsGraphIso
    (source (graph core0621) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1522.graph sourceMap0621=true := by decide +kernel
theorem fusedMap0621_checked : acceptsGraphIso
    (fused (graph core0621) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1068.graph fusedMap0621=true := by decide +kernel
theorem certified0621 : Certified (graph core0621) (root 10) 2 2 :=
  of_native_maps core0621 DegreeOneMiddleResidualSpectrum1522.graph DegreeOneMiddleResidualSpectrum1068.graph
    sourceMap0621 fusedMap0621 sourceMap0621_checked fusedMap0621_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0621
#print axioms sourceMap0621_checked
#print axioms fusedMap0621_checked
#print axioms certified0621
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
