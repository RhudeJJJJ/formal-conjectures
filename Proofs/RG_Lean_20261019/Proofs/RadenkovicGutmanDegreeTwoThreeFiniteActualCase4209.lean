/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4209 : Family 9 := level9.get ⟨83,by decide⟩
def sourceMap4209 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4209 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4209_checked : acceptsGraphIso
    (source (graph core4209) (root 9) 2 2) DegreeTwoThreeSpectrum4514.graph sourceMap4209=true := by decide +kernel
theorem fusedMap4209_checked : acceptsGraphIso
    (fused (graph core4209) (root 9) 2 2) DegreeTwoThreeSpectrum4035.graph fusedMap4209=true := by decide +kernel
theorem certified4209 : Certified (graph core4209) (root 9) 2 2 :=
  of_native_maps core4209 DegreeTwoThreeSpectrum4514.graph DegreeTwoThreeSpectrum4035.graph
    sourceMap4209 fusedMap4209 sourceMap4209_checked fusedMap4209_checked
    DegreeTwoThreeFiniteComparisons.comparison4209
#print axioms sourceMap4209_checked
#print axioms fusedMap4209_checked
#print axioms certified4209
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
