/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4248 : Family 9 := level9.get ⟨210,by decide⟩
def sourceMap4248 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,14,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4248 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4248_checked : acceptsGraphIso
    (source (graph core4248) (root 9) 2 2) DegreeTwoThreeSpectrum4813.graph sourceMap4248=true := by decide +kernel
theorem fusedMap4248_checked : acceptsGraphIso
    (fused (graph core4248) (root 9) 2 2) DegreeTwoThreeSpectrum3994.graph fusedMap4248=true := by decide +kernel
theorem certified4248 : Certified (graph core4248) (root 9) 2 2 :=
  of_native_maps core4248 DegreeTwoThreeSpectrum4813.graph DegreeTwoThreeSpectrum3994.graph
    sourceMap4248 fusedMap4248 sourceMap4248_checked fusedMap4248_checked
    DegreeTwoThreeFiniteComparisons.comparison4248
#print axioms sourceMap4248_checked
#print axioms fusedMap4248_checked
#print axioms certified4248
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
