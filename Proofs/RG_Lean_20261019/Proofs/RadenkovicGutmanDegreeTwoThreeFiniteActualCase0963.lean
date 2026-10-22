/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0963 : Family 10 := level10.get ⟨1607,by decide⟩
def sourceMap0963 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0963 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0963_checked : acceptsGraphIso
    (source (graph core0963) (root 10) 0 0) DegreeTwoThreeSpectrum1321.graph sourceMap0963=true := by decide +kernel
theorem fusedMap0963_checked : acceptsGraphIso
    (fused (graph core0963) (root 10) 0 0) DegreeTwoThreeSpectrum1313.graph fusedMap0963=true := by decide +kernel
theorem certified0963 : Certified (graph core0963) (root 10) 0 0 :=
  of_native_maps core0963 DegreeTwoThreeSpectrum1321.graph DegreeTwoThreeSpectrum1313.graph
    sourceMap0963 fusedMap0963 sourceMap0963_checked fusedMap0963_checked
    DegreeTwoThreeFiniteComparisons.comparison0963
#print axioms sourceMap0963_checked
#print axioms fusedMap0963_checked
#print axioms certified0963
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
