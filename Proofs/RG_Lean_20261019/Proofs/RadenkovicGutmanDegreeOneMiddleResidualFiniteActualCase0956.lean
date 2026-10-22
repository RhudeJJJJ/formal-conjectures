/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0956 : Family 10 := level10.get ⟨784,by decide⟩
def sourceMap0956 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0956 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0956_checked : acceptsGraphIso
    (source (graph core0956) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2244.graph sourceMap0956=true := by decide +kernel
theorem fusedMap0956_checked : acceptsGraphIso
    (fused (graph core0956) (root 10) 2 2) DegreeTwoThreeSpectrum5565.graph fusedMap0956=true := by decide +kernel
theorem certified0956 : Certified (graph core0956) (root 10) 2 2 :=
  of_native_maps core0956 DegreeOneMiddleResidualSpectrum2244.graph DegreeTwoThreeSpectrum5565.graph
    sourceMap0956 fusedMap0956 sourceMap0956_checked fusedMap0956_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0956
#print axioms sourceMap0956_checked
#print axioms fusedMap0956_checked
#print axioms certified0956
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
