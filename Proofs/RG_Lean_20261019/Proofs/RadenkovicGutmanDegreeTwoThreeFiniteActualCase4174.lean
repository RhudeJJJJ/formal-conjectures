/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4174 : Family 8 := level8.get ⟨222,by decide⟩
def sourceMap4174 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4174 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4174_checked : acceptsGraphIso
    (source (graph core4174) (root 8) 2 2) DegreeTwoThreeSpectrum3812.graph sourceMap4174=true := by decide +kernel
theorem fusedMap4174_checked : acceptsGraphIso
    (fused (graph core4174) (root 8) 2 2) DegreeTwoThreeSpectrum2561.graph fusedMap4174=true := by decide +kernel
theorem certified4174 : Certified (graph core4174) (root 8) 2 2 :=
  of_native_maps core4174 DegreeTwoThreeSpectrum3812.graph DegreeTwoThreeSpectrum2561.graph
    sourceMap4174 fusedMap4174 sourceMap4174_checked fusedMap4174_checked
    DegreeTwoThreeFiniteComparisons.comparison4174
#print axioms sourceMap4174_checked
#print axioms fusedMap4174_checked
#print axioms certified4174
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
