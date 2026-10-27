/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4772 : Family 10 := level10.get ⟨1061,by decide⟩
def sourceMap4772 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4772 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4772_checked : acceptsGraphIso
    (source (graph core4772) (root 10) 2 2) DegreeTwoThreeSpectrum7139.graph sourceMap4772=true := by decide +kernel
theorem fusedMap4772_checked : acceptsGraphIso
    (fused (graph core4772) (root 10) 2 2) DegreeTwoThreeSpectrum6107.graph fusedMap4772=true := by decide +kernel
theorem certified4772 : Certified (graph core4772) (root 10) 2 2 :=
  of_native_maps core4772 DegreeTwoThreeSpectrum7139.graph DegreeTwoThreeSpectrum6107.graph
    sourceMap4772 fusedMap4772 sourceMap4772_checked fusedMap4772_checked
    DegreeTwoThreeFiniteComparisons.comparison4772
#print axioms sourceMap4772_checked
#print axioms fusedMap4772_checked
#print axioms certified4772
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
