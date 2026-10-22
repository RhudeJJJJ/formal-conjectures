/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4842 : Family 10 := level10.get ⟨1226,by decide⟩
def sourceMap4842 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4842 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4842_checked : acceptsGraphIso
    (source (graph core4842) (root 10) 2 2) DegreeTwoThreeSpectrum7231.graph sourceMap4842=true := by decide +kernel
theorem fusedMap4842_checked : acceptsGraphIso
    (fused (graph core4842) (root 10) 2 2) DegreeTwoThreeSpectrum6428.graph fusedMap4842=true := by decide +kernel
theorem certified4842 : Certified (graph core4842) (root 10) 2 2 :=
  of_native_maps core4842 DegreeTwoThreeSpectrum7231.graph DegreeTwoThreeSpectrum6428.graph
    sourceMap4842 fusedMap4842 sourceMap4842_checked fusedMap4842_checked
    DegreeTwoThreeFiniteComparisons.comparison4842
#print axioms sourceMap4842_checked
#print axioms fusedMap4842_checked
#print axioms certified4842
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
