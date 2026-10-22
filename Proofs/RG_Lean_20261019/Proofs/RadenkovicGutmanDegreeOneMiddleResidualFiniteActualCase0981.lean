/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0981 : Family 10 := level10.get ⟨847,by decide⟩
def sourceMap0981 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0981 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0981_checked : acceptsGraphIso
    (source (graph core0981) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2280.graph sourceMap0981=true := by decide +kernel
theorem fusedMap0981_checked : acceptsGraphIso
    (fused (graph core0981) (root 10) 2 2) DegreeTwoThreeSpectrum5680.graph fusedMap0981=true := by decide +kernel
theorem certified0981 : Certified (graph core0981) (root 10) 2 2 :=
  of_native_maps core0981 DegreeOneMiddleResidualSpectrum2280.graph DegreeTwoThreeSpectrum5680.graph
    sourceMap0981 fusedMap0981 sourceMap0981_checked fusedMap0981_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0981
#print axioms sourceMap0981_checked
#print axioms fusedMap0981_checked
#print axioms certified0981
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
