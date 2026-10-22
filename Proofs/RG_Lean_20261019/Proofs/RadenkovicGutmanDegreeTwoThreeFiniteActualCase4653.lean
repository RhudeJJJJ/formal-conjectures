/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4653 : Family 10 := level10.get ⟨754,by decide⟩
def sourceMap4653 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4653 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4653_checked : acceptsGraphIso
    (source (graph core4653) (root 10) 2 2) DegreeTwoThreeSpectrum7421.graph sourceMap4653=true := by decide +kernel
theorem fusedMap4653_checked : acceptsGraphIso
    (fused (graph core4653) (root 10) 2 2) DegreeTwoThreeSpectrum5520.graph fusedMap4653=true := by decide +kernel
theorem certified4653 : Certified (graph core4653) (root 10) 2 2 :=
  of_native_maps core4653 DegreeTwoThreeSpectrum7421.graph DegreeTwoThreeSpectrum5520.graph
    sourceMap4653 fusedMap4653 sourceMap4653_checked fusedMap4653_checked
    DegreeTwoThreeFiniteComparisons.comparison4653
#print axioms sourceMap4653_checked
#print axioms fusedMap4653_checked
#print axioms certified4653
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
