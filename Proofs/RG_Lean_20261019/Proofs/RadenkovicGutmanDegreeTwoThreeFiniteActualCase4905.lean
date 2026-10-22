/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4905 : Family 10 := level10.get ⟨1379,by decide⟩
def sourceMap4905 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4905 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4905_checked : acceptsGraphIso
    (source (graph core4905) (root 10) 2 2) DegreeTwoThreeSpectrum7268.graph sourceMap4905=true := by decide +kernel
theorem fusedMap4905_checked : acceptsGraphIso
    (fused (graph core4905) (root 10) 2 2) DegreeTwoThreeSpectrum6730.graph fusedMap4905=true := by decide +kernel
theorem certified4905 : Certified (graph core4905) (root 10) 2 2 :=
  of_native_maps core4905 DegreeTwoThreeSpectrum7268.graph DegreeTwoThreeSpectrum6730.graph
    sourceMap4905 fusedMap4905 sourceMap4905_checked fusedMap4905_checked
    DegreeTwoThreeFiniteComparisons.comparison4905
#print axioms sourceMap4905_checked
#print axioms fusedMap4905_checked
#print axioms certified4905
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
