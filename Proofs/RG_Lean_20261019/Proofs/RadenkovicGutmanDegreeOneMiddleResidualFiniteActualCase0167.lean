/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0167 : Family 8 := level8.get ⟨209,by decide⟩
def sourceMap0167 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0167 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0167_checked : acceptsGraphIso
    (source (graph core0167) (root 8) 2 2) DegreeOneMiddleResidualSpectrum351.graph sourceMap0167=true := by decide +kernel
theorem fusedMap0167_checked : acceptsGraphIso
    (fused (graph core0167) (root 8) 2 2) DegreeTwoThreeSpectrum2506.graph fusedMap0167=true := by decide +kernel
theorem certified0167 : Certified (graph core0167) (root 8) 2 2 :=
  of_native_maps core0167 DegreeOneMiddleResidualSpectrum351.graph DegreeTwoThreeSpectrum2506.graph
    sourceMap0167 fusedMap0167 sourceMap0167_checked fusedMap0167_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0167
#print axioms sourceMap0167_checked
#print axioms fusedMap0167_checked
#print axioms certified0167
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
