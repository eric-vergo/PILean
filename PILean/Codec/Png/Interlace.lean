import PILean.Core.Error

/-!
# Adam7 deinterlacing

Decode-only for v1 (the encoder never interlaces, matching Pillow's
default). Owned by WP12; the pass structure, per-pass filtering, and the
deinterlace entry point are internal to the PNG decoder and not part of
the frozen interface — WP12 shapes this module freely.
-/

