/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4781 : Family 10 := level10.get ⟨1082,by decide⟩
def sourceMap4781 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4781 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4781_checked : acceptsGraphIso
    (source (graph core4781) (root 10) 2 2) DegreeTwoThreeSpectrum7162.graph sourceMap4781=true := by decide +kernel
theorem fusedMap4781_checked : acceptsGraphIso
    (fused (graph core4781) (root 10) 2 2) DegreeTwoThreeSpectrum6147.graph fusedMap4781=true := by decide +kernel
theorem certified4781 : Certified (graph core4781) (root 10) 2 2 :=
  of_native_maps core4781 DegreeTwoThreeSpectrum7162.graph DegreeTwoThreeSpectrum6147.graph
    sourceMap4781 fusedMap4781 sourceMap4781_checked fusedMap4781_checked
    DegreeTwoThreeFiniteComparisons.comparison4781
#print axioms sourceMap4781_checked
#print axioms fusedMap4781_checked
#print axioms certified4781
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
