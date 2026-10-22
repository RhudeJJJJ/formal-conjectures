/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0228 : Family 9 := level9.get ⟨35,by decide⟩
def sourceMap0228 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0228 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0228_checked : acceptsGraphIso
    (source (graph core0228) (root 9) 2 2) DegreeTwoThreeSpectrum4561.graph sourceMap0228=true := by decide +kernel
theorem fusedMap0228_checked : acceptsGraphIso
    (fused (graph core0228) (root 9) 2 2) DegreeTwoThreeSpectrum3884.graph fusedMap0228=true := by decide +kernel
theorem certified0228 : Certified (graph core0228) (root 9) 2 2 :=
  of_native_maps core0228 DegreeTwoThreeSpectrum4561.graph DegreeTwoThreeSpectrum3884.graph
    sourceMap0228 fusedMap0228 sourceMap0228_checked fusedMap0228_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0228
#print axioms sourceMap0228_checked
#print axioms fusedMap0228_checked
#print axioms certified0228
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
