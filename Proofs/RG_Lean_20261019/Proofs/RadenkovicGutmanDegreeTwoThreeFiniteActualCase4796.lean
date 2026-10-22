/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4796 : Family 10 := level10.get ⟨1122,by decide⟩
def sourceMap4796 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4796 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4796_checked : acceptsGraphIso
    (source (graph core4796) (root 10) 2 2) DegreeTwoThreeSpectrum7203.graph sourceMap4796=true := by decide +kernel
theorem fusedMap4796_checked : acceptsGraphIso
    (fused (graph core4796) (root 10) 2 2) DegreeTwoThreeSpectrum6230.graph fusedMap4796=true := by decide +kernel
theorem certified4796 : Certified (graph core4796) (root 10) 2 2 :=
  of_native_maps core4796 DegreeTwoThreeSpectrum7203.graph DegreeTwoThreeSpectrum6230.graph
    sourceMap4796 fusedMap4796 sourceMap4796_checked fusedMap4796_checked
    DegreeTwoThreeFiniteComparisons.comparison4796
#print axioms sourceMap4796_checked
#print axioms fusedMap4796_checked
#print axioms certified4796
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
