/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4790 : Family 10 := level10.get ⟨1108,by decide⟩
def sourceMap4790 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4790 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4790_checked : acceptsGraphIso
    (source (graph core4790) (root 10) 2 2) DegreeTwoThreeSpectrum7188.graph sourceMap4790=true := by decide +kernel
theorem fusedMap4790_checked : acceptsGraphIso
    (fused (graph core4790) (root 10) 2 2) DegreeTwoThreeSpectrum6201.graph fusedMap4790=true := by decide +kernel
theorem certified4790 : Certified (graph core4790) (root 10) 2 2 :=
  of_native_maps core4790 DegreeTwoThreeSpectrum7188.graph DegreeTwoThreeSpectrum6201.graph
    sourceMap4790 fusedMap4790 sourceMap4790_checked fusedMap4790_checked
    DegreeTwoThreeFiniteComparisons.comparison4790
#print axioms sourceMap4790_checked
#print axioms fusedMap4790_checked
#print axioms certified4790
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
