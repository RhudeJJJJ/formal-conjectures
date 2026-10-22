/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4642 : Family 10 := level10.get ⟨719,by decide⟩
def sourceMap4642 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,14,15,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4642 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4642_checked : acceptsGraphIso
    (source (graph core4642) (root 10) 2 2) DegreeTwoThreeSpectrum7374.graph sourceMap4642=true := by decide +kernel
theorem fusedMap4642_checked : acceptsGraphIso
    (fused (graph core4642) (root 10) 2 2) DegreeTwoThreeSpectrum5466.graph fusedMap4642=true := by decide +kernel
theorem certified4642 : Certified (graph core4642) (root 10) 2 2 :=
  of_native_maps core4642 DegreeTwoThreeSpectrum7374.graph DegreeTwoThreeSpectrum5466.graph
    sourceMap4642 fusedMap4642 sourceMap4642_checked fusedMap4642_checked
    DegreeTwoThreeFiniteComparisons.comparison4642
#print axioms sourceMap4642_checked
#print axioms fusedMap4642_checked
#print axioms certified4642
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
