/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4923 : Family 10 := level10.get ⟨1427,by decide⟩
def sourceMap4923 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,8,9,10,11,12,13,14,15,16,7,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4923 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4923_checked : acceptsGraphIso
    (source (graph core4923) (root 10) 2 2) DegreeTwoThreeSpectrum7524.graph sourceMap4923=true := by decide +kernel
theorem fusedMap4923_checked : acceptsGraphIso
    (fused (graph core4923) (root 10) 2 2) DegreeTwoThreeSpectrum6882.graph fusedMap4923=true := by decide +kernel
theorem certified4923 : Certified (graph core4923) (root 10) 2 2 :=
  of_native_maps core4923 DegreeTwoThreeSpectrum7524.graph DegreeTwoThreeSpectrum6882.graph
    sourceMap4923 fusedMap4923 sourceMap4923_checked fusedMap4923_checked
    DegreeTwoThreeFiniteComparisons.comparison4923
#print axioms sourceMap4923_checked
#print axioms fusedMap4923_checked
#print axioms certified4923
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
