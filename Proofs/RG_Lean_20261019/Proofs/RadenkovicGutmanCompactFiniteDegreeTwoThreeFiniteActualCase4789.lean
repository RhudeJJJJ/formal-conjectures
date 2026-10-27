/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4789 : Family 10 := level10.get ⟨1105,by decide⟩
def sourceMap4789 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4789 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4789_checked : acceptsGraphIso
    (source (graph core4789) (root 10) 2 2) DegreeTwoThreeSpectrum7185.graph sourceMap4789=true := by decide +kernel
theorem fusedMap4789_checked : acceptsGraphIso
    (fused (graph core4789) (root 10) 2 2) DegreeTwoThreeSpectrum6195.graph fusedMap4789=true := by decide +kernel
theorem certified4789 : Certified (graph core4789) (root 10) 2 2 :=
  of_native_maps core4789 DegreeTwoThreeSpectrum7185.graph DegreeTwoThreeSpectrum6195.graph
    sourceMap4789 fusedMap4789 sourceMap4789_checked fusedMap4789_checked
    DegreeTwoThreeFiniteComparisons.comparison4789
#print axioms sourceMap4789_checked
#print axioms fusedMap4789_checked
#print axioms certified4789
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
