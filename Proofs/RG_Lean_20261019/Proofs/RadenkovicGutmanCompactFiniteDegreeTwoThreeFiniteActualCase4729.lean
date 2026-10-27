/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4729 : Family 10 := level10.get ⟨952,by decide⟩
def sourceMap4729 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4729 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4729_checked : acceptsGraphIso
    (source (graph core4729) (root 10) 2 2) DegreeTwoThreeSpectrum7516.graph sourceMap4729=true := by decide +kernel
theorem fusedMap4729_checked : acceptsGraphIso
    (fused (graph core4729) (root 10) 2 2) DegreeTwoThreeSpectrum5852.graph fusedMap4729=true := by decide +kernel
theorem certified4729 : Certified (graph core4729) (root 10) 2 2 :=
  of_native_maps core4729 DegreeTwoThreeSpectrum7516.graph DegreeTwoThreeSpectrum5852.graph
    sourceMap4729 fusedMap4729 sourceMap4729_checked fusedMap4729_checked
    DegreeTwoThreeFiniteComparisons.comparison4729
#print axioms sourceMap4729_checked
#print axioms fusedMap4729_checked
#print axioms certified4729
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
