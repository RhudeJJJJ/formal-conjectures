/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4953 : Family 10 := level10.get ⟨1495,by decide⟩
def sourceMap4953 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4953 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4953_checked : acceptsGraphIso
    (source (graph core4953) (root 10) 2 2) DegreeTwoThreeSpectrum7132.graph sourceMap4953=true := by decide +kernel
theorem fusedMap4953_checked : acceptsGraphIso
    (fused (graph core4953) (root 10) 2 2) DegreeTwoThreeSpectrum6998.graph fusedMap4953=true := by decide +kernel
theorem certified4953 : Certified (graph core4953) (root 10) 2 2 :=
  of_native_maps core4953 DegreeTwoThreeSpectrum7132.graph DegreeTwoThreeSpectrum6998.graph
    sourceMap4953 fusedMap4953 sourceMap4953_checked fusedMap4953_checked
    DegreeTwoThreeFiniteComparisons.comparison4953
#print axioms sourceMap4953_checked
#print axioms fusedMap4953_checked
#print axioms certified4953
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
