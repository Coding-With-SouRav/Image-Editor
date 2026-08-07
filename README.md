# Image Editor Features Overview

This Tkinter-based image editor offers a comprehensive suite of editing tools with a modern dark-themed interface. Here are its key features:

#### **Core Functionality**
1. **File Operations**
   - Import images via drag-and-drop or file browser (Ctrl+B)
   - Export in PNG (transparency support), JPG (high quality), or ICO (icon) formats
   - Compression options: Quality reduction or resizing
   - Image info display (dimensions, format, size)

2. **Editing Tools**
   - **Crop**: Interactive crop with draggable handles
   - **Rotate**: Slider-based rotation (±180°) with flip controls
   - **Reset**: Revert to original image
   - **Erase**: Brush tool with adjustable size (5-200px)

3. **Background Processing**
   - Background removal (AI-powered via `rembg`)
   - Custom background color selection
   - Transparency support (checkerboard preview)
   - Restore original background

4. **History Management**
   - 20-step undo/redo (Ctrl+Z/Ctrl+Y)
   - Visual history tracking

#### **Adjustments & Filters**
1. **Basic Adjustments**
   - Exposure
   - Brightness
   - Contrast
   - Saturation
   - Sharpness

2. **Advanced Filters** (Organized in categories)
   - *Popular*: Arctic, Cobalt, Harvest, Noir, Bloom
   - *Film*: R600, P100F, KC64, V-250
   - *Portrait*: Starlight, Azure, Oxygen, Mint
   - *Creative*: Vignette, Vintage, Neon, Grainy
   - *Seasonal*: Spring, Summer, Autumn, Winter
   - +50+ specialized filters

3. **Real-time Previews**
   - Interactive sliders for all adjustments
   - Filter thumbnail previews

#### **Interface Features**
- **Modern Dark UI**: Custom theme with purple/blue accents
- **Responsive Design**: Panels resize dynamically
- **Zoom/Pan**: Mouse wheel zoom (10-100%) + drag panning
- **Animated Transitions**: Smooth effect panel expansions
- **Drag-and-Drop**: Intuitive file import
- **Keyboard Shortcuts**: All major actions have hotkeys

#### **Technical Highlights**
- **Efficient Rendering**: Uses PIL/Pillow for image processing
- **Cross-Platform**: Works on Windows/macOS/Linux
- **Resource Management**: Handles bundled assets properly
- **State Preservation**: Remembers window size/location
- **Threaded Operations**: Background processing for heavy tasks (e.g., AI removal)

#### **Specialized Tools**
- **Doodle Mode**: Freehand drawing (in development)
- **Vignette Editor**: Custom darkness control
- **Selective Color Adjustments**: Highlights/shadows
- **Film Grain/Texture Effects**


The editor combines professional-grade features with an accessible interface, suitable for both quick edits and advanced photo manipulation. Its modular design allows easy expansion of filters and tools.

# Demo Images


![Screenshot 2025-07-03 112025](https://github.com/user-attachments/assets/3357bf51-f90f-4c0d-b00f-aa485ef3b417)
![Screenshot 2025-07-03 112737](https://github.com/user-attachments/assets/2fff100b-7412-4b39-a533-5f29ff7db667)
![Screenshot 2025-07-03 112835](https://github.com/user-attachments/assets/69e197fc-0e45-4b35-9711-5e320fda09b9)
![Screenshot 2025-07-03 112903](https://github.com/user-attachments/assets/35a8b311-9b88-4cce-9a58-c1cee43151bf)
![Screenshot 2025-07-03 112924](https://github.com/user-attachments/assets/0e23b009-83d1-4386-9cda-d4f9033464f6)
![Screenshot 2025-07-03 112956](https://github.com/user-attachments/assets/22e6e386-7ff7-48bc-a73f-3002a162cf95)
![Screenshot 2025-07-03 113340](https://github.com/user-attachments/assets/6ff86eae-d927-49d9-a442-5ba4f0fdd68e)
![Screenshot 2025-07-03 113416](https://github.com/user-attachments/assets/4ec149fe-6716-476e-a729-53535f6e82ab)

![Screenshot 2025-07-03 113049](https://github.com/user-attachments/assets/2511296b-b97a-47e5-ad48-b0c1e16352d0)
![Screenshot 2025-07-03 113129](https://github.com/user-attachments/assets/b32c21f3-c031-4fa3-8bfc-5e0da73dfa9b)
![Screenshot 2025-07-03 113238](https://github.com/user-attachments/assets/60a88ae6-fe53-44c5-b31a-94f3abeabcc1)
![Screenshot 2025-07-03 113307](https://github.com/user-attachments/assets/a9bfbbe2-6f19-4ce2-9b04-73af42a793c6)
![Screenshot 2025-07-03 113812](https://github.com/user-attachments/assets/a7a6b85f-768c-479f-b255-cf2965c5d8b6)
![Screenshot 2025-07-03 113632](https://github.com/user-attachments/assets/66420e8e-2431-4f70-96e1-fb4ebfe48e5d)


