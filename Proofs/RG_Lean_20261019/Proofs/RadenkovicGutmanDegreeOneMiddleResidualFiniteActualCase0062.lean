/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0062 : Family 8 := level8.get ⟨3,by decide⟩
def sourceMap0062 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,3,4,5,6,7,8] (sourceLabel 8 2 2 v)
def fusedMap0062 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0062_checked : acceptsGraphIso
    (source (graph core0062) (root 8) 2 2) DegreeOneMiddleResidualSpectrum243.graph sourceMap0062=true := by decide +kernel
theorem fusedMap0062_checked : acceptsGraphIso
    (fused (graph core0062) (root 8) 2 2) DegreeTwoThreeSpectrum2311.graph fusedMap0062=true := by decide +kernel
theorem certified0062 : Certified (graph core0062) (root 8) 2 2 :=
  of_native_maps core0062 DegreeOneMiddleResidualSpectrum243.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap0062 fusedMap0062 sourceMap0062_checked fusedMap0062_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0062
#print axioms sourceMap0062_checked
#print axioms fusedMap0062_checked
#print axioms certified0062
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
