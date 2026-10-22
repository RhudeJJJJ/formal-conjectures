/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0963 : Family 10 := level10.get ⟨802,by decide⟩
def sourceMap0963 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0963 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0963_checked : acceptsGraphIso
    (source (graph core0963) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2251.graph sourceMap0963=true := by decide +kernel
theorem fusedMap0963_checked : acceptsGraphIso
    (fused (graph core0963) (root 10) 2 2) DegreeTwoThreeSpectrum5598.graph fusedMap0963=true := by decide +kernel
theorem certified0963 : Certified (graph core0963) (root 10) 2 2 :=
  of_native_maps core0963 DegreeOneMiddleResidualSpectrum2251.graph DegreeTwoThreeSpectrum5598.graph
    sourceMap0963 fusedMap0963 sourceMap0963_checked fusedMap0963_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0963
#print axioms sourceMap0963_checked
#print axioms fusedMap0963_checked
#print axioms certified0963
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
