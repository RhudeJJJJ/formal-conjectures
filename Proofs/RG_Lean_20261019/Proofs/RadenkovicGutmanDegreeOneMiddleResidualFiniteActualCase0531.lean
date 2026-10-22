/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0531 : Family 10 := level10.get ⟨57,by decide⟩
def sourceMap0531 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0531 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0531_checked : acceptsGraphIso
    (source (graph core0531) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1592.graph sourceMap0531=true := by decide +kernel
theorem fusedMap0531_checked : acceptsGraphIso
    (fused (graph core0531) (root 10) 2 2) DegreeTwoThreeSpectrum4969.graph fusedMap0531=true := by decide +kernel
theorem certified0531 : Certified (graph core0531) (root 10) 2 2 :=
  of_native_maps core0531 DegreeOneMiddleResidualSpectrum1592.graph DegreeTwoThreeSpectrum4969.graph
    sourceMap0531 fusedMap0531 sourceMap0531_checked fusedMap0531_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0531
#print axioms sourceMap0531_checked
#print axioms fusedMap0531_checked
#print axioms certified0531
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
