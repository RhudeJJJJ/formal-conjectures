/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0134 : Family 8 := level8.get ⟨115,by decide⟩
def sourceMap0134 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0134 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0134_checked : acceptsGraphIso
    (source (graph core0134) (root 8) 2 2) DegreeOneMiddleResidualSpectrum285.graph sourceMap0134=true := by decide +kernel
theorem fusedMap0134_checked : acceptsGraphIso
    (fused (graph core0134) (root 8) 2 2) DegreeTwoThreeSpectrum2536.graph fusedMap0134=true := by decide +kernel
theorem certified0134 : Certified (graph core0134) (root 8) 2 2 :=
  of_native_maps core0134 DegreeOneMiddleResidualSpectrum285.graph DegreeTwoThreeSpectrum2536.graph
    sourceMap0134 fusedMap0134 sourceMap0134_checked fusedMap0134_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0134
#print axioms sourceMap0134_checked
#print axioms fusedMap0134_checked
#print axioms certified0134
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
