/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4782 : Family 10 := level10.get ⟨1085,by decide⟩
def sourceMap4782 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4782 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4782_checked : acceptsGraphIso
    (source (graph core4782) (root 10) 2 2) DegreeTwoThreeSpectrum7173.graph sourceMap4782=true := by decide +kernel
theorem fusedMap4782_checked : acceptsGraphIso
    (fused (graph core4782) (root 10) 2 2) DegreeTwoThreeSpectrum6153.graph fusedMap4782=true := by decide +kernel
theorem certified4782 : Certified (graph core4782) (root 10) 2 2 :=
  of_native_maps core4782 DegreeTwoThreeSpectrum7173.graph DegreeTwoThreeSpectrum6153.graph
    sourceMap4782 fusedMap4782 sourceMap4782_checked fusedMap4782_checked
    DegreeTwoThreeFiniteComparisons.comparison4782
#print axioms sourceMap4782_checked
#print axioms fusedMap4782_checked
#print axioms certified4782
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
