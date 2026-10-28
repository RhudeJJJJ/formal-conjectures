/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4938 : Family 10 := level10.get ⟨1459,by decide⟩
def sourceMap4938 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,8,9,10,11,12,13,14,15,16,7,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4938 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4938_checked : acceptsGraphIso
    (source (graph core4938) (root 10) 2 2) DegreeTwoThreeSpectrum7535.graph sourceMap4938=true := by decide +kernel
theorem fusedMap4938_checked : acceptsGraphIso
    (fused (graph core4938) (root 10) 2 2) DegreeTwoThreeSpectrum6932.graph fusedMap4938=true := by decide +kernel
theorem certified4938 : Certified (graph core4938) (root 10) 2 2 :=
  of_native_maps core4938 DegreeTwoThreeSpectrum7535.graph DegreeTwoThreeSpectrum6932.graph
    sourceMap4938 fusedMap4938 sourceMap4938_checked fusedMap4938_checked
    DegreeTwoThreeFiniteComparisons.comparison4938
#print axioms sourceMap4938_checked
#print axioms fusedMap4938_checked
#print axioms certified4938
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
