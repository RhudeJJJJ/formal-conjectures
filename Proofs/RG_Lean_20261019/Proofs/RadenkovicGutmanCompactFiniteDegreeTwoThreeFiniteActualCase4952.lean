/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4952 : Family 10 := level10.get ⟨1494,by decide⟩
def sourceMap4952 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4952 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4952_checked : acceptsGraphIso
    (source (graph core4952) (root 10) 2 2) DegreeTwoThreeSpectrum7098.graph sourceMap4952=true := by decide +kernel
theorem fusedMap4952_checked : acceptsGraphIso
    (fused (graph core4952) (root 10) 2 2) DegreeTwoThreeSpectrum6996.graph fusedMap4952=true := by decide +kernel
theorem certified4952 : Certified (graph core4952) (root 10) 2 2 :=
  of_native_maps core4952 DegreeTwoThreeSpectrum7098.graph DegreeTwoThreeSpectrum6996.graph
    sourceMap4952 fusedMap4952 sourceMap4952_checked fusedMap4952_checked
    DegreeTwoThreeFiniteComparisons.comparison4952
#print axioms sourceMap4952_checked
#print axioms fusedMap4952_checked
#print axioms certified4952
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
