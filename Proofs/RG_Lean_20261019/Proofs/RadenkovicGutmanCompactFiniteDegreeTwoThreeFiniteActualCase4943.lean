/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4943 : Family 10 := level10.get ⟨1467,by decide⟩
def sourceMap4943 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4943 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4943_checked : acceptsGraphIso
    (source (graph core4943) (root 10) 2 2) DegreeTwoThreeSpectrum7271.graph sourceMap4943=true := by decide +kernel
theorem fusedMap4943_checked : acceptsGraphIso
    (fused (graph core4943) (root 10) 2 2) DegreeTwoThreeSpectrum6947.graph fusedMap4943=true := by decide +kernel
theorem certified4943 : Certified (graph core4943) (root 10) 2 2 :=
  of_native_maps core4943 DegreeTwoThreeSpectrum7271.graph DegreeTwoThreeSpectrum6947.graph
    sourceMap4943 fusedMap4943 sourceMap4943_checked fusedMap4943_checked
    DegreeTwoThreeFiniteComparisons.comparison4943
#print axioms sourceMap4943_checked
#print axioms fusedMap4943_checked
#print axioms certified4943
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
