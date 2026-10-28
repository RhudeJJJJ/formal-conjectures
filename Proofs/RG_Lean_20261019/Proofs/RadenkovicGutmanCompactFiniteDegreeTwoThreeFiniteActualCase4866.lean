/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4866 : Family 10 := level10.get ⟨1289,by decide⟩
def sourceMap4866 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4866 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4866_checked : acceptsGraphIso
    (source (graph core4866) (root 10) 2 2) DegreeTwoThreeSpectrum7266.graph sourceMap4866=true := by decide +kernel
theorem fusedMap4866_checked : acceptsGraphIso
    (fused (graph core4866) (root 10) 2 2) DegreeTwoThreeSpectrum6563.graph fusedMap4866=true := by decide +kernel
theorem certified4866 : Certified (graph core4866) (root 10) 2 2 :=
  of_native_maps core4866 DegreeTwoThreeSpectrum7266.graph DegreeTwoThreeSpectrum6563.graph
    sourceMap4866 fusedMap4866 sourceMap4866_checked fusedMap4866_checked
    DegreeTwoThreeFiniteComparisons.comparison4866
#print axioms sourceMap4866_checked
#print axioms fusedMap4866_checked
#print axioms certified4866
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
