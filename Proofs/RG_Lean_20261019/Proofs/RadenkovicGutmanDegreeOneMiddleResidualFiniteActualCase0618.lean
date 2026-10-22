/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0618 : Family 10 := level10.get ⟨178,by decide⟩
def sourceMap0618 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,9,10,11,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0618 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0618_checked : acceptsGraphIso
    (source (graph core0618) (root 10) 2 2) DegreeTwoThreeSpectrum6861.graph sourceMap0618=true := by decide +kernel
theorem fusedMap0618_checked : acceptsGraphIso
    (fused (graph core0618) (root 10) 2 2) DegreeTwoThreeSpectrum5125.graph fusedMap0618=true := by decide +kernel
theorem certified0618 : Certified (graph core0618) (root 10) 2 2 :=
  of_native_maps core0618 DegreeTwoThreeSpectrum6861.graph DegreeTwoThreeSpectrum5125.graph
    sourceMap0618 fusedMap0618 sourceMap0618_checked fusedMap0618_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0618
#print axioms sourceMap0618_checked
#print axioms fusedMap0618_checked
#print axioms certified0618
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
